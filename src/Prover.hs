{-# LANGUAGE RecordWildCards #-}
module Prover where

import Control.Monad (when, replicateM, foldM)
import Control.Monad.RWS.Strict (RWS, ask, get, put, runRWS, tell)
import qualified Data.Heap as H
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import qualified Data.Set as HS  -- using a second alias for clarity on key set
import Data.Maybe (fromMaybe)
import Data.List (intercalate, (\\), sort)

import Types
import DebugLog (dtrace)
import Matching

-- Prover monad
type ProverM = RWS Engine [TraceEvent] Env

-- Environment operations
emptyEnv :: Env
emptyEnv = Env S.empty M.empty S.empty H.empty 0 0 S.empty M.empty M.empty

-- Instrumentation: track theorem application counts (in-memory only; not persisted)
type ThmCounters = M.Map String Int

data IterMetrics = IterMetrics
  { imIteration :: !Int
  , imStartFactCount :: !Int
  , imEndFactCount :: !Int
  , imAppliedTheorems :: !Int
  } deriving (Show)

data EngineMetrics = EngineMetrics
  { emThmCounts :: ThmCounters
  , emIterations :: [IterMetrics]
  }

emptyEngineMetrics :: EngineMetrics
emptyEngineMetrics = EngineMetrics M.empty []

-- Canonical fact insertion with dependency merging.
-- Keyed only by (predicate, args); if an existing fact matches structurally,
-- we merge dependency sets and keep the original provenance.
insertFact :: Fact -> Env -> (Env, Bool)
insertFact fact env@Env{..} =
  let key = (fPred fact, fArgs fact)
  in case M.lookup key eFactIndex of
      Nothing ->
        let env' = env { eFacts = S.insert fact eFacts
                       , eFactIndex = M.insert key fact eFactIndex }
        in (env', True)
      Just existing ->
        let mergedDeps = S.union (fDeps existing) (fDeps fact)
        in if mergedDeps == fDeps existing
             then (env, False) -- no new info
             else let updated = existing { fDeps = mergedDeps }
                      facts' = S.insert updated (S.delete existing eFacts)
                      env' = env { eFacts = facts'
                                 , eFactIndex = M.insert key updated eFactIndex }
                  in (env', False) -- structurally same, treat as not new

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
    -- No queue update in breadth-first mode
    tell [TraceFactInserted 
      { teThm = "DEBUG"
      , teFact = mkFactP PFalse []
      , teParentDeps = S.empty
      , teParents = []
      , teSubs = M.fromList [("fact_added", predToString (fPred fact)), ("total_facts", show factCount)]
      }]
  when (isContradiction fact) $ handleContradiction fact
  return added

handleContradiction :: Fact -> ProverM ()
handleContradiction contraFact = do
  let deps = fDeps contraFact
  env <- get
  let hasGlobal = any (\f -> isContradiction f && S.null (fDeps f)) (eFacts env)
  if S.null deps
    then return () -- already a global contradiction
    else do
      -- Inject a global contradiction fact (dep-free) if not present
      if not hasGlobal
        then do
          -- Preserve the provenance from the original contradiction
          let globalFact = contraFact { fDeps = S.empty }
          _ <- insertFactM globalFact
          tell [TraceFactInserted { teThm = "BACKTRACK", teFact = globalFact, teParentDeps = S.empty, teParents = [], teSubs = M.fromList [("lifted_branch_contradiction","true"),("deps", show (S.toList deps))] }]
          return ()
        else return ()

insertDisjM :: Disj -> ProverM [Fact]
insertDisjM disj = do
  env <- get
  let sig = canonicalDisjSignature (dAlts disj)
  case M.lookup sig (eDisjIndex env) of
    -- Disjunction already exists: do nothing (canonicalization) and return empty list
    Just _existingDid -> return []
    Nothing -> do
      let newDid = dId disj
          env1 = env { eDisjs = M.insert newDid disj (eDisjs env)
                     , eDisjIndex = M.insert sig newDid (eDisjIndex env) }
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

-- Build a canonical signature string for a disjunction's alternatives (predicate+args sorted)
canonicalDisjSignature :: [Fact] -> String
canonicalDisjSignature alts =
  let factKey (Fact p as _ _) = predToString p ++ "(" ++ intercalate "," (map renderValue as) ++ ")"
  in intercalate "|" (sort (map factKey alts))

-- Breadth-first proof search (like Python auto_solve)
proveLoop :: ProverM ()
proveLoop = proveLoopBFS 0

proveLoopBFS :: Int -> ProverM ()
proveLoopBFS iteration = do
  env <- get
  engine <- ask
  let anyContradiction = any isContradiction (eFacts env)
      globalContradiction = any (\f -> isContradiction f && S.null (fDeps f)) (eFacts env)
      maxRoundsLimit = maxRounds engine
  
  if globalContradiction || anyContradiction
    then do
      tell [TraceFactInserted { teThm = "DEBUG", teFact = mkFactP PFalse [], teParentDeps = S.empty, teParents = [], teSubs = M.fromList [("contradiction_found","true"),("global", show globalContradiction)] }]
      return ()
    else if iteration >= maxRoundsLimit
      then do
        tell [TraceFactInserted { teThm = "DEBUG", teFact = mkFactP PFalse [], teParentDeps = S.empty, teParents = [], teSubs = M.fromList [("max_iterations_reached", show maxRoundsLimit)] }]
        return ()
      else do
        -- Breadth-first: apply all possible theorems once per iteration
        newFactsAdded <- applyAllTheoremsOnce iteration
        if not newFactsAdded
          then do
            tell [TraceFactInserted { teThm = "DEBUG", teFact = mkFactP PFalse [], teParentDeps = S.empty, teParents = [], teSubs = M.fromList [("no_new_facts","true"),("iteration", show iteration)] }]
            return ()
          else do
            tell [TraceFactInserted { teThm = "DEBUG", teFact = mkFactP PFalse [], teParentDeps = S.empty, teParents = [], teSubs = M.fromList [("iteration", show iteration),("total_facts", show (S.size (eFacts env)))] }]
            proveLoopBFS (iteration + 1)

-- Apply all theorems once per iteration (breadth-first like Python)
applyAllTheoremsOnce :: Int -> ProverM Bool
applyAllTheoremsOnce iter = do
  engine <- ask
  env <- get
  let facts = S.toList (eFacts env)
      factsByPredName = M.fromListWith (++) [(predToString (fPred f), [f]) | f <- facts]
  
  -- Generate all possible applications for all theorems
  let allAppsRaw = concatMap (generateAllApplications factsByPredName) (thms engine)
      allApps    = dedupApplications allAppsRaw
  
  -- Limit applications per theorem to prevent runaway generation
  let limitedApps = limitApplicationsPerTheorem allApps
  
  -- Apply each application and track if any new facts were added
  newFactsAdded <- foldM applyAndCheck False limitedApps
  -- Emit instrumentation event summarizing this iteration's theorem attempts
  let appsByThm = M.fromListWith (+) [(appThmName app, 1 :: Int) | (_, app) <- limitedApps]
      meta = M.fromList [("iter", show iter)
                        ,("apps", show (length limitedApps))
                        ,("distinct_theorems", show (M.size appsByThm))]
  tell [TraceFactInserted { teThm = "INSTRUMENT", teFact = mkFactP PFalse [], teParentDeps = S.empty, teParents = [], teSubs = meta }]
  mapM_ (emitPerThm iter) (M.toList appsByThm)
  return newFactsAdded
  where
    applyAndCheck hasNewFacts (_, app) = do
      env1 <- get
      let factCountBefore = S.size (eFacts env1)
      applyTheoremOutput app
      env2 <- get
      let factCountAfter = S.size (eFacts env2)
      return $ hasNewFacts || (factCountAfter > factCountBefore)
    emitPerThm :: Int -> (String, Int) -> ProverM ()
    emitPerThm i (tn,c) =
      tell [TraceFactInserted { teThm = "THM_COUNT"
                              , teFact = mkFactP PFalse []
                              , teParentDeps = S.empty
                              , teParents = []
                              , teSubs = M.fromList [("iter", show i),("theorem", tn),("applications", show c)]
                              }]

-- Limit the number of applications per theorem per iteration to prevent explosions
limitApplicationsPerTheorem :: [(Int, App)] -> [(Int, App)]
limitApplicationsPerTheorem apps = 
  let groupByThm = M.fromListWith (++) [(appThmName app, [(cost, app)]) | (cost, app) <- apps]
      limitPerThm = 50  -- Allow up to 50 applications per theorem per iteration
      limitedGroups = M.map (take limitPerThm) groupByThm
  in concat (M.elems limitedGroups)

-- No longer needed for breadth-first search - facts are processed each iteration
updateQueueWithNewFact :: Fact -> ProverM ()
updateQueueWithNewFact _ = return () -- No-op in breadth-first approach

tryApplyTheorem :: Theorem -> [Fact] -> [(Int, App)]
tryApplyTheorem thm@Theorem{..} tuple =
  case matchTemplate tuple tTemplate of
    Left _ -> []
    Right substitution ->
      let concreteTuple = map (substFact substitution) tuple
          parentDeps = S.unions (map fDeps concreteTuple)
          outputs = tApply concreteTuple
      in if null outputs
           then []
           else let debugMsg = "APPLYING THEOREM: " ++ tName ++ "\n  facts: " ++ show concreteTuple ++ "\n  outputs: " ++ show outputs
                in dtrace debugMsg $ map (outputToApp parentDeps concreteTuple substitution) outputs
  where
    outputToApp deps parents subs out =
      let debugFactMsg = case out of
            TOFact f -> "  GENERATED FACT: " ++ show f
            TODisj fs -> "  GENERATED DISJUNCTION: " ++ show fs
      in dtrace debugFactMsg (tCost, app)
      where
        app = App
          { appThmName = tName
          , appOutput  = out
          , appDeps    = deps
          , appParents = parents
          , appSubs    = subs
          }

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
          sig = canonicalDisjSignature materializedAlts
      case M.lookup sig (eDisjIndex env) of
        Just _existing -> return () -- already have this disjunction; skip entirely
        Nothing -> do
          let disj = Disj 
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
          _alts <- insertDisjM disj
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

-- No longer needed - breadth-first search doesn't use a pre-populated queue
initialPopulateQueue :: ProverM ()
initialPopulateQueue = do
  env <- get
  let facts = S.toList (eFacts env)
  
  tell [TraceFactInserted 
    { teThm = "DEBUG"
    , teFact = mkFactP PFalse [] -- dummy fact for debug
    , teParentDeps = S.empty
    , teParents = []
    , teSubs = M.fromList [("initial_facts", show (length facts)), ("breadth_first_mode", "true")]
    }]

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

-- Deduplicate applications by a lightweight structural key: theorem name + output head predicate + parent preds
-- Stronger application deduplication: collapse by theorem + normalized output only.
-- Ignores differing parents / substitutions that lead to identical produced facts/disjunctions.
dedupApplications :: [(Int, App)] -> [(Int, App)]
dedupApplications apps = M.elems $ foldl step M.empty apps
  where
    step acc pair@(_cost, app@App{..}) =
      let key = appThmName ++ "|" ++ outKey appOutput
      in M.insertWith (\_ old -> old) key pair acc
    outKey (TOFact (Fact p as _ _)) = "F:" ++ predToString p ++ "(" ++ intercalate "," (map renderValue as) ++ ")"
    outKey (TODisj facts) =
      let alts = map factKey facts
      in "D:{" ++ intercalate "|" (sort alts) ++ "}"
    factKey (Fact p as _ _) = predToString p ++ "(" ++ intercalate "," (map renderValue as) ++ ")"