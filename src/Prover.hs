import Control.Monad (when, replicateM)
import Control.Monad.RWS.Strict (RWS, ask, get, put, runRWS, tell)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Data.List (intercalate, (\\))

import Types
import Matching

-- Prover monad
type ProverM = RWS Engine [TraceEvent] Env

-- Environment operations
emptyEnv :: Env
emptyEnv = Env S.empty M.empty S.empty 0 0

insertFact :: Fact -> Env -> (Env, Bool)
insertFact fact env@Env{..}
  | fact `S.member` eFacts = (env, False)
  | otherwise = ( env { eFacts = S.insert fact eFacts
                      , eFrontier = S.insert fact eFrontier 
                      }, True)

insertDisj :: Disj -> Env -> (Env, [Fact])
insertDisj disj@Disj{..} env0 = (env', taggedAlternatives)
  where
    env1 = env0 { eDisjs = M.insert dId disj (eDisjs env0) }
    
    tagAlternative ix alternative =
      let altProvenance = case dProv of
            Just prov@ProvTheorem{..} -> 
              Just prov { fromDisj = Just (dId, ix) }
            other -> other
          newDeps = S.unions [fDeps alternative, dDeps, S.singleton (dId, ix)]
      in alternative { fDeps = newDeps, fProv = altProvenance }
    
    taggedAlternatives = zipWith tagAlternative [0..] dAlts
    (env', _) = foldl (\(e,_) f -> insertFact f e) (env1, False) taggedAlternatives

-- Fresh name generation
freshName :: String -> Env -> (String, Env)
freshName prefix env@Env{..} = 
  (prefix ++ show eFresh, env { eFresh = eFresh + 1 })

-- Wildcard materialization
materializeWildcards :: [Fact] -> Env -> ([Fact], Env)
materializeWildcards facts env0 = (map substituteFact facts, finalEnv)
  where
    wildcards = filter isWildcard $ concatMap fArgs facts
    (finalEnv, substitutions) = foldl processWildcard (env0, M.empty) wildcards
    
    processWildcard (e, subs) wildcard
      | wildcard `M.member` subs = (e, subs)
      | otherwise = 
          let baseName = if null (drop 1 wildcard) then "X" else drop 1 wildcard ++ "_"
              (newName, e') = freshName baseName e
          in (e', M.insert wildcard newName subs)
    
    substituteFact (Fact n as deps prov) = 
      Fact n (map (\x -> M.findWithDefault x x substitutions) as) deps prov

-- Monadic operations
insertFactM :: Fact -> ProverM Bool
insertFactM fact = do
  env <- get
  let (env', added) = insertFact fact env
  put env'
  when added $ tell [TraceFactInserted 
    { teThm = "(insert)"
    , teFact = fact
    , teParentDeps = fDeps fact
    , teParents = []
    , teSubs = M.empty
    }]
  return added

insertDisjM :: Disj -> ProverM [Fact]
insertDisjM disj = do
  env <- get
  let (env', alts) = insertDisj disj env
  put env'
  let subs = case dProv disj of
               Just ProvTheorem{provSubs = Just s} -> s
               _ -> M.empty
  tell [TraceDisjInserted 
    { teThm = fromMaybe "(disj)" (dLabel disj)
    , teDid = dId disj
    , teLabel = dLabel disj
    , teAlts = dAlts disj
    , teDeps = dDeps disj
    , teSubs = subs
    }]
  return alts

-- Generate tuples for semi-naive evaluation
incrementalTuples :: Int -> [a] -> [a] -> [[a]]
incrementalTuples 0 _ _ = [[]]
incrementalTuples k old new =
  -- Tuples with a new fact at the head
  [n : rest | n <- new, rest <- replicateM (k-1) (old ++ new)]
  ++
  -- Tuples with an old fact at the head, and at least one new fact in the tail
  [o : rest | o <- old, rest <- incrementalTuples (k-1) old new]

-- Single proof step
stepRoundM :: ProverM ()
stepRoundM = do
  engine <- ask
  env0 <- get
  
  if S.null (eFrontier env0)
    then put env0 { eFrontier = S.empty }
    else do
      let oldFacts = S.toList (S.difference (eFacts env0) (eFrontier env0))
          newFacts = S.toList (eFrontier env0)
          
      -- Find all theorem applications
      let findApplications theorem@Theorem{..} =
            let Template patterns = tTemplate
                tupleSize = length patterns
                -- Use incremental tuples for semi-naive evaluation
                candidateTuples = incrementalTuples tupleSize oldFacts newFacts
            in concatMap (tryApplyTheorem theorem) candidateTuples
          
          tryApplyTheorem Theorem{..} tuple = 
            case matchTemplate tuple tTemplate of
              Nothing -> []
              Just substitution ->
                let concreteTuple = map (substFact substitution) tuple
                    parentDeps = S.unions (map fDeps concreteTuple)
                    outputs = tApply concreteTuple
                in map (\out -> (tName, out, parentDeps, concreteTuple, substitution)) outputs
      
      let allApplications = concatMap findApplications (thms engine)
      
      -- Apply each theorem result
      mapM_ applyTheoremOutput allApplications
      
      -- Update frontier
      finalEnv <- get
      put finalEnv { eFrontier = S.difference (eFacts finalEnv) (eFacts env0) }

-- Apply a single theorem output
applyTheoremOutput :: (String, ThmOut, S.Set Dep, [Fact], Subst) -> ProverM ()
applyTheoremOutput (theoremName, output, parentDeps, parents, substitution) =
  case output of
    TOFact fact -> do
      materializedFacts <- materializeWildcardsM [fact]
      let factWithProvenance = (head materializedFacts) 
            { fDeps = parentDeps
            , fProv = Just ProvTheorem 
                { thmName = theoremName
                , parentFacts = parents
                , fromDisj = Nothing
                , provSubs = Just substitution
                }
            }
      _ <- insertFactM factWithProvenance
      return ()
    
    TODisj alternatives -> do
      materializedAlts <- materializeWildcardsM alternatives
      env <- get
      let label = Just $ theoremName ++ "(" ++ intercalate ", " 
                    (map (\f -> fName f ++ show (fArgs f)) parents) ++ ")"
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
      _ <- insertDisjM disj
      env' <- get
      put env' { eNextDid = eNextDid env' + 1 }

materializeWildcardsM :: [Fact] -> ProverM [Fact]
materializeWildcardsM facts = do
  env <- get
  let (facts', env') = materializeWildcards facts env
  put env'
  return facts'