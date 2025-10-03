{-# LANGUAGE RecordWildCards #-}
module Prover where

import Control.Monad (when, replicateM)
import Control.Monad.RWS.Strict (RWS, ask, get, put, runRWS, tell)
import qualified Data.Heap as H
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
emptyEnv = Env S.empty M.empty S.empty H.empty 0 0

insertFact :: Fact -> Env -> (Env, Bool)
insertFact fact env@Env{..}
  | fact `S.member` eFacts = (env, False)
  | otherwise = 
      let env' = env { eFacts = S.insert fact eFacts }
      in (env', True)

insertDisj :: Disj -> Env -> (Env, [Fact])
insertDisj disj@Disj{..} env0 = (env', taggedAlternatives)
  where
    env1 = env0 { eDisjs = M.insert dId disj (eDisjs env0) }
    
    tagAlternative ix alternative =
      let altProvenance = case dProv of
            Just prov@ProvTheorem{..} -> 
              Just prov { fromDisj = Just (dId, ix) }
            other -> other
          newDeps = S.unions [fDeps alternative, dDeps, S.singleton (mkDep dId ix)]
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
    isWildcard (Sym s) = not (null s) && head s == '_'
    isWildcard _ = False
    wildcards = filter isWildcard $ concatMap fArgs facts
    (finalEnv, substitutions) = foldl processWildcard (env0, M.empty) wildcards
    processWildcard (e, subs) wildcard@(Sym s)
      | wildcard `M.member` subs = (e, subs)
      | otherwise = 
          let baseName = if null (drop 1 s) then "X" else drop 1 s ++ "_"
              (newName, e') = freshName baseName e
          in (e', M.insert wildcard (Sym newName) subs)
    processWildcard (e, subs) _ = (e, subs)
    substituteFact (Fact p as deps prov) = 
      Fact p (map (\x -> M.findWithDefault x x substitutions) as) deps prov

-- Monadic operations
insertFactM :: Fact -> ProverM Bool
insertFactM fact = do
  env <- get
  let (env', added) = insertFact fact env
  put env'
  when added $ do
    tell [TraceFactInserted 
      { teThm = "(insert)"
      , teFact = fact
      , teParentDeps = fDeps fact
      , teParents = []
      , teSubs = M.empty
      }]
    env <- get
    let factCount = S.size (eFacts env)
    updateQueueWithNewFact fact
    env' <- get
    let queueSize = H.size (eAppQueue env')
    tell [TraceFactInserted 
      { teThm = "DEBUG"
      , teFact = mkFactP PFalse []
      , teParentDeps = S.empty
      , teParents = []
      , teSubs = M.fromList [("fact_added", predToString (fPred fact)), ("total_facts", show factCount), ("queue_size", show queueSize)]
      }]
  return added

insertDisjM :: Disj -> ProverM [Fact]
insertDisjM disj = do
  env <- get
  let env1 = env { eDisjs = M.insert (dId disj) disj (eDisjs env) }
  put env1
  
  -- Tag alternatives with proper dependencies and provenance
  let tagAlternative ix alternative =
        let altProvenance = case dProv disj of
              Just prov@ProvTheorem{..} -> 
                Just prov { fromDisj = Just (dId disj, ix) }
              other -> other
            newDeps = S.unions [fDeps alternative, dDeps disj, S.singleton (mkDep (dId disj) ix)]
        in alternative { fDeps = newDeps, fProv = altProvenance }
      
      taggedAlternatives = zipWith tagAlternative [0..] (dAlts disj)
  
  -- Insert each alternative using insertFactM to trigger new applications
  mapM_ insertFactM taggedAlternatives
  
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
  return taggedAlternatives

-- Single proof step (now the main loop)
proveLoop :: ProverM ()
proveLoop = do
  env <- get
  case H.view (eAppQueue env) of
    Nothing -> do
      tell [TraceFactInserted 
        { teThm = "DEBUG"
        , teFact = mkFactP PFalse []
        , teParentDeps = S.empty
        , teParents = []
        , teSubs = M.fromList [("queue_empty", "true"), ("total_facts", show (S.size (eFacts env)))]
        }]
      return () -- Queue is empty, we are done
    Just ((cost, app), newQueue) -> do
      put env { eAppQueue = newQueue }
      
      tell [TraceFactInserted 
        { teThm = "DEBUG"
        , teFact = mkFactP PFalse []
        , teParentDeps = S.empty
        , teParents = []
        , teSubs = M.fromList [("applying", appThmName app), ("cost", show cost)]
        }]
      
      -- Apply the theorem
      applyTheoremOutput app
      
      -- Check for contradiction
      env' <- get
      let contradictionFound = any isContradiction (eFacts env')
      
      when contradictionFound $ do
        tell [TraceFactInserted 
          { teThm = "DEBUG"
          , teFact = mkFactP PFalse []
          , teParentDeps = S.empty
          , teParents = []
          , teSubs = M.fromList [("contradiction_found", "true")]
          }]
      
      -- Continue if no contradiction is found
      when (not contradictionFound) proveLoop

-- Find new applications for a fact and add them to the queue
updateQueueWithNewFact :: Fact -> ProverM ()
updateQueueWithNewFact newFact = do
  engine <- ask
  env <- get
  let facts = S.toList (eFacts env)
  
  let findApps thm@Theorem{..} =
        let TTemplate patterns = tTemplate
            k = length patterns
            factsByPredName = M.fromListWith (++) [(predToString (fPred f), [f]) | f <- facts]
            -- For each position where newFact could fit
            tuplesThatIncludeNewFact = 
              [ tuple
              | i <- [0..k-1]
              , let patternAtI = patterns !! i
              , predToString (fPred newFact) == tpName patternAtI  -- newFact matches pattern at position i
              , let otherPatterns = take i patterns ++ drop (i+1) patterns
              , let otherCandidates = [ M.findWithDefault [] (tpName p) factsByPredName | p <- otherPatterns ]
              , otherFacts <- cartesian otherCandidates
              , let tuple = take i otherFacts ++ [newFact] ++ drop i otherFacts
              , length tuple == k
              ]
        in if k == 0
           then []
           else [(thm, tuple) | tuple <- tuplesThatIncludeNewFact]
  
  let allPotentialApps = concatMap findApps (thms engine)
  
  let newApps = concatMap (uncurry tryApplyTheorem) allPotentialApps
  
  let newQueue = foldl (\q (cost, app) -> H.insert (cost, app) q) (eAppQueue env) newApps
  put env { eAppQueue = newQueue }

tryApplyTheorem :: Theorem -> [Fact] -> [(Int, App)]
tryApplyTheorem thm@Theorem{..} tuple =
  case matchTemplate tuple tTemplate of
    Left _ -> []
    Right substitution ->
      let concreteTuple = map (substFact substitution) tuple
          parentDeps = S.unions (map fDeps concreteTuple)
          outputs = tApply concreteTuple
      in map (outputToApp parentDeps concreteTuple substitution) outputs
  where
    outputToApp deps parents subs out =
      let app = App
            { appThmName = tName
            , appOutput  = out
            , appDeps    = deps
            , appParents = parents
            , appSubs    = subs
            }
      in (tCost, app)

isContradiction :: Fact -> Bool
isContradiction (Fact (PFalse) _ _ _) = True
isContradiction _ = False

-- Apply a single theorem output
applyTheoremOutput :: App -> ProverM ()
applyTheoremOutput App{..} =
  case appOutput of
    TOFact fact -> do
      materializedFacts <- materializeWildcardsM [fact]
      let factWithProvenance = (head materializedFacts) 
            { fDeps = appDeps
            , fProv = Just ProvTheorem 
                { thmName = appThmName
                , parentFacts = appParents
                , fromDisj = Nothing
                , provSubs = Just appSubs
                }
            }
      _ <- insertFactM factWithProvenance
      return ()
    
    TODisj alternatives -> do
      materializedAlts <- materializeWildcardsM alternatives
      env <- get
      let canonAlt f = predToString (fPred f) ++ "(" ++ intercalate "," (map renderValue (fArgs f)) ++ ")"
          label = Just $ "{" ++ intercalate " | " (map canonAlt materializedAlts) ++ "}"
          disj = Disj 
            { dId = eNextDid env
            , dAlts = materializedAlts
            , dDeps = appDeps
            , dProv = Just ProvTheorem 
                { thmName = appThmName
                , parentFacts = appParents
                , fromDisj = Nothing
                , provSubs = Just appSubs
                }
            , dLabel = label
            }
      alts <- insertDisjM disj
      -- When a disjunction is added, its alternatives are also added as facts.
      -- The `insertFactM` call for them will trigger `updateQueueWithNewFact`.
      env' <- get
      put env' { eNextDid = eNextDid env' + 1 }

-- Materialize wildcards within the ProverM monad
materializeWildcardsM :: [Fact] -> ProverM [Fact]
materializeWildcardsM facts = do
  env <- get
  let (facts', env') = materializeWildcards facts env
  put env'
  return facts'

-- Main entry point for running the prover
runProver :: Engine -> Env -> (Env, [TraceEvent])
runProver engine env =
  let (_, finalEnv, trace) = runRWS proveLoop engine env
  in (finalEnv, trace)

-- Initial population of the queue
initialPopulateQueue :: ProverM ()
initialPopulateQueue = do
  engine <- ask
  env <- get
  let facts = S.toList (eFacts env)
      factsByPredName = M.fromListWith (++) [(predToString (fPred f), [f]) | f <- facts]
  
  tell [TraceFactInserted 
    { teThm = "DEBUG"
    , teFact = mkFactP PFalse [] -- dummy fact for debug
    , teParentDeps = S.empty
    , teParents = []
    , teSubs = M.fromList [("initial_facts", show (length facts))]
    }]
  
  -- Generate all possible theorem applications from existing facts
  let allApps = concatMap (generateAllApplications factsByPredName) (thms engine)
  let newQueue = foldl (\q (cost, app) -> H.insert (cost, app) q) (eAppQueue env) allApps
  
  tell [TraceFactInserted 
    { teThm = "DEBUG"
    , teFact = mkFactP PFalse [] -- dummy fact for debug
    , teParentDeps = S.empty
    , teParents = []
    , teSubs = M.fromList [("initial_apps", show (length allApps))]
    }]
  
  put env { eAppQueue = newQueue }

-- Generate all possible applications of a theorem given available facts
generateAllApplications :: M.Map String [Fact] -> Theorem -> [(Int, App)]
generateAllApplications factsByPredName thm@Theorem{..} =
  let TTemplate patterns = tTemplate
      k = length patterns
      candidates = [ M.findWithDefault [] (tpName p) factsByPredName | p <- patterns ]
  in if k == 0
     then []
     else concatMap (tryApplyTheorem thm) (cartesian candidates)

-- Helper for combinations
combinations :: Int -> [a] -> [[a]]
combinations 0 _ = [[]]
combinations _ [] = []
combinations k (x:xs) = map (x:) (combinations (k-1) xs) ++ combinations k xs

-- Helper for cartesian product
cartesian :: [[a]] -> [[a]]
cartesian [] = [[]]
cartesian (x:xs) = [y:ys | y <- x, ys <- cartesian xs]