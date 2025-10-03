-- | Pure state-based proving engine
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module PureProver where

import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad (foldM, when)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Heap as H
-- import Data.Maybe (fromMaybe)
import Data.List (intercalate)

import Types 
  ( Fact(..)
  , Pred(..)
  , Value(..)
  , predToString
  , renderValue
  , TTemplate(..)
  , TPattern(..)
  , ValuePat(..)
  , Theorem(..)
  , ThmOut(..)
  , Env(..)
  , Disj(..)
  , Dep(..)
  , mkDep
  , depDisjInt
  , depAltInt
  , Provenance(..)
  , Subst
  , TraceEvent(..)
  )
import Errors  
import Matching
-- | Generate candidate tuples that match pattern fact names (prunes search drastically)
generateTuplesForTemplate :: [Fact] -> TTemplate -> [[Fact]]
generateTuplesForTemplate facts (TTemplate patterns) =
  let arities = [ (tpName p, length (tpArgs p)) | p <- patterns ]
  in sequence [ filter (\f -> predToString (fPred f) == nm && length (fArgs f) == ar) facts
              | (nm, ar) <- arities
              ]

-- | Helper to lift ProverResult into ProverM
liftError :: ProverResult a -> ProverM a
liftError (Right x) = return x
liftError (Left err) = throwError err

-- | Pure prover monad combining State and Error handling
newtype ProverM a = ProverM (ExceptT ProverError (State Env) a)
  deriving (Functor, Applicative, Monad, MonadState Env, MonadError ProverError)

-- | Run the prover computation
runProverM :: ProverM a -> Env -> (Either ProverError a, Env)
runProverM (ProverM computation) env = runState (runExceptT computation) env

-- | Environment operations
emptyEnv :: Env
emptyEnv = Env S.empty M.empty S.empty H.empty 0 0

-- | Pure fact insertion
insertFact :: Fact -> ProverM Bool  
insertFact fact = do
  env@Env{..} <- get
  if fact `S.member` eFacts
    then return False
    else do
      put env { eFacts = S.insert fact eFacts
              , eFrontier = S.insert fact eFrontier }
      return True

-- | Pure disjunction insertion
insertDisj :: Disj -> ProverM [Fact]
insertDisj disj@Disj{..} = do
  env0 <- get
  let env1 = env0 { eDisjs = M.insert dId disj (eDisjs env0) }
  put env1
  
  let tagAlternative ix alternative = do
        let altProvenance = case dProv of
              Just prov@ProvTheorem{..} -> 
                Just prov { fromDisj = Just (dId, ix) }
              other -> other
            newDeps = S.unions [fDeps alternative, dDeps, S.singleton (mkDep dId ix)]
        return alternative { fDeps = newDeps, fProv = altProvenance }
  
  taggedAlts <- mapM (uncurry tagAlternative) (zip [0..] dAlts)
  mapM_ insertFact taggedAlts
  return taggedAlts

-- | Generate fresh names
freshName :: String -> ProverM String
freshName prefix = do
  env@Env{..} <- get
  put env { eFresh = eFresh + 1 }
  return $ prefix ++ show eFresh

-- | Materialize wildcards in facts
materializeWildcards :: [Fact] -> ProverM [Fact]
materializeWildcards facts = do
  let wildcards = filter isWildcardValue $ concatMap fArgs facts
  substitutions <- foldM processWildcard M.empty wildcards
  return $ map (substituteFact substitutions) facts
  where
    -- A wildcard is a Sym starting with '_'
    isWildcardValue (Sym s) = not (null s) && head s == '_'
    isWildcardValue _ = False

    processWildcard subs wildcard@(Sym s)
      | wildcard `M.member` subs = return subs
      | otherwise = do
          let baseName = if null (drop 1 s) then "X" else drop 1 s ++ "_"
          newName <- freshName baseName
          return $ M.insert wildcard (Sym newName) subs
    processWildcard subs _ = return subs  -- Only Sym wildcards are processed

    substituteFact subs (Fact n as deps prov) =
      Fact n (map (\x -> M.findWithDefault x x subs) as) deps prov

-- | Generate ordered tuples efficiently using lazy evaluation
orderedTuples :: Int -> [a] -> [[a]]
orderedTuples 0 _ = [[]]
orderedTuples _ [] = []
orderedTuples k xs = [x:ys | x <- xs, ys <- orderedTuples (k-1) xs]

-- | Apply a single theorem to facts with error handling
applyTheorem :: Theorem -> [Fact] -> ProverM [ThmOut]
applyTheorem theorem@Theorem{..} facts = do
  substitution <- liftError $ matchTemplate facts tTemplate
  let concreteFacts = map (substFact substitution) facts
      outputs = tApply concreteFacts
  return outputs

-- | Process theorem outputs into the environment  
processTheoremOutput :: String -> ThmOut -> S.Set Dep -> [Fact] -> Subst -> ProverM ()
processTheoremOutput theoremName output parentDeps parents substitution = do
  case output of
    TOFact fact -> do
      materializedFacts <- materializeWildcards [fact]
      factWithMeta <- liftError $ safeHead "materialized facts" materializedFacts
      let factWithProvenance = factWithMeta
            { fDeps = parentDeps
            , fProv = Just ProvTheorem 
                { thmName = theoremName
                , parentFacts = parents
                , fromDisj = Nothing
                , provSubs = Just substitution
                }
            }
      _ <- insertFact factWithProvenance
      return ()
    
    TODisj alternatives -> do
      materializedAlts <- materializeWildcards alternatives
      env <- get
      let canonAlt f = predToString (fPred f) ++ "(" ++ intercalate "," (map renderValue (fArgs f)) ++ ")"
          label = Just $ "{" ++ intercalate " | " (map canonAlt materializedAlts) ++ "}"
          disj = Disj 
            { dId = eNextDid env
            , dAlts = materializedAlts
            , dDeps = parentDeps
            , dProv = Just ProvTheorem 
                { thmName = theoremName
                , parentFacts = parents
                , fromDisj = Nothing
                , provSubs = Just substitution
                }
            , dLabel = label
            }
      _ <- insertDisj disj
      modify $ \e -> e { eNextDid = eNextDid e + 1 }

-- | Single proof step using lazy evaluation
stepRound :: [Theorem] -> ProverM Bool
stepRound theorems = do
  env0 <- get
  
  if S.null (eFrontier env0)
    then do
      modify (\env -> env { eFrontier = S.empty })
      return False
    else do
      let factsList = S.toList (eFacts env0)
      
      -- Simple theorem applications with pruned tuple enumeration by fact names
      let tryOne theorem =
            let candidateTuples = take 10000 (generateTuplesForTemplate factsList (tTemplate theorem))
                appsForTuple tuple =
                  case matchTemplate tuple (tTemplate theorem) of
                    Right subst ->
                      let outputs = tApply theorem tuple
                          parentDeps = S.unions (map fDeps tuple)
                      in [ (tName theorem, out, parentDeps, tuple, subst) | out <- outputs ]
                    Left _ -> []
            in concatMap appsForTuple candidateTuples
          tryApplications = concatMap tryOne theorems

      -- Process applications  
      hasWork <- foldM processApplication False (take 1000 tryApplications) -- Increased limit
      
      -- Update frontier
      finalEnv <- get
      modify (\env -> env { eFrontier = S.difference (eFacts finalEnv) (eFacts env0) })
      return hasWork
  where
    processApplication hasWork (theoremName, output, parentDeps, parents, substitution) = do
      processTheoremOutput theoremName output parentDeps parents substitution
      return True

-- | Main proof search with timeout and resource limits
proveGoal :: [Theorem] -> Fact -> Int -> ProverM Bool
proveGoal theorems goal maxRounds = do
  searchLoop maxRounds
  where
    searchLoop 0 = throwError $ TimeoutError maxRounds
    searchLoop n = do
      hasWork <- stepRound theorems
      if not hasWork
        then return False  -- No more work to do
        else do
          proven <- checkGoalProven goal
          if proven
            then return True
            else searchLoop (n - 1)

-- | Check if goal is proven
checkGoalProven :: Fact -> ProverM Bool
checkGoalProven goalFact = do
  env@Env{..} <- get
  let instances = [f | f <- S.toList eFacts, 
                      fPred f == fPred goalFact, 
                      fArgs f == fArgs goalFact]
  
  if null instances
    then return False
    else do
      let allDeps = S.unions (map fDeps instances)
          disjIds = S.toList (S.map depDisjInt allDeps)
          arities = [(did, length (case M.lookup did eDisjs of
                                     Just disj -> dAlts disj
                                     Nothing -> [])) 
                    | did <- disjIds]
      
      -- Check for contradictions (empty disjunctions)
      if any (\(_, arity) -> arity == 0) arities
        then return True
        -- Check for direct proofs (no dependencies)  
        else if null disjIds
          then return $ any (S.null . fDeps) instances
          -- Check complex disjunction-based proofs (simplified)
          else if length disjIds > 10  -- Limit case splits
            then return False
            else do
              let assignments = cartesian [[i | i <- [0..arity-1]] | (_, arity) <- arities]
                  disjIdsList = map fst arities
                  ok assignment = 
                    let assignSet = S.fromList (zip disjIdsList assignment)
                        asDeps = S.fromList [ mkDep did idx | (did, idx) <- S.toList assignSet ]
                    in any (\inst -> fDeps inst `S.isSubsetOf` asDeps) instances
              return $ not (null assignments) && all ok assignments

-- Helper function for cartesian product  
cartesian :: [[a]] -> [[a]]
cartesian [] = [[]]
cartesian (xs:xss) = [x:ys | x <- xs, ys <- cartesian xss]

-- | Convert old RWS-based operations to new pure ones
liftOldProver :: IO (Bool, Env, [TraceEvent]) -> [Theorem] -> [Fact] -> Fact -> (Either ProverError Bool, Env)
liftOldProver _ theorems hypotheses goal = 
  let env0 = foldr addHypothesis emptyEnv hypotheses
      addHypothesis hyp env = 
        let (env', _) = runProverM (insertFact (hyp { fProv = Just ProvHypothesis })) env
        in case env' of
             Right _ -> env  -- This is simplified - should handle properly
             Left _ -> env
      proverAction = proveGoal theorems goal 50
  in runProverM proverAction env0