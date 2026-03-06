{-# LANGUAGE BangPatterns #-}

-- | Automated theorem proving via forward chaining.
--
-- This module implements the main proof search loop using an agenda-based
-- approach. New facts trigger theorem matching via 'IncrementalMatching',
-- and derived conclusions are added to the work queue until either:
--
--   * The goal is proven (all disjunction branches covered)
--   * The work queue is exhausted
--   * The iteration limit is reached
--
module Auto
  ( SolverConfig(..)
  , SolverStats(..)
  , SearchStatus(..)
  , OutputMode(..)
  , defaultConfig
  , autoSolve
  , autoSolveWith
  , autoSolveWithStats
  , solveWithStatsPure
  , matchFactsToTheorem
  , solveOrder
  , printHashBuckets
  ) where

-- Standard library
import Data.Foldable (toList)
import Data.List (sortOn)
import Data.Maybe (listToMaybe)
import qualified Data.Sequence as Seq
import qualified Data.IntSet as IntSet
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set
import qualified Data.DList as DL

-- Local modules
import Core
import Env
import EnvPrint (printRelevantFacts)
import ProofTree (renderTree, renderClean)
import Environment.Types (EnvStats(..), peFactIndex, BookkeepingState(..))
import IncrementalMatching (findTriggeredMatches, matchPremises)
import ProofMonad (runProofM)
import Environment.FactsMonadic (applyThmM)
import Predicates (falseFact, group, order, simple)
import Theorems (thmList, thmNames)

data SearchStatus
  = GoalFound
  | QueueExhausted
  | IterationLimitReached
  deriving (Eq, Show)

-- | Output mode for proof display
data OutputMode
  = OutputClassic    -- Original verbose output
  | OutputClean      -- Cleaner formatting with case labels (Option B)
  | OutputTree       -- Tree visualization (Option D)
  deriving (Eq, Show)

data SolverConfig = SolverConfig
  { scMaxIterations :: Int
  , scBatchSize :: Int
  , scVerbose :: Bool           -- Print stats during/after solving
  , scDumpHashBuckets :: Bool   -- Dump hash bucket distribution
  , scOutputMode :: OutputMode  -- How to display the proof
  } deriving (Eq, Show)

defaultConfig :: SolverConfig
defaultConfig = SolverConfig
  { scMaxIterations = 1000
  , scBatchSize = 8
  , scVerbose = False
  , scDumpHashBuckets = False
  , scOutputMode = OutputClean  -- Use clean output by default
  }

-- | Statistics collected during solving
data SolverStats = SolverStats
  { ssIterations :: !Int          -- Total iterations
  , ssQueueHighWater :: !Int      -- Maximum queue length reached
  , ssFinalQueueLen :: !Int       -- Final queue length
  , ssFinalEnvStats :: EnvStats   -- Final environment stats
  } deriving (Eq, Show)

data SearchState = SearchState
  { ssEnv :: !ProofEnvironment    -- Strict to prevent heap accumulation
  , ssQueue :: !(Seq.Seq FactEntry)  -- Strict sequence
  , ssProcessed :: !IntSet.IntSet  -- Use IntSet for faster membership tests
  , ssClosedBranches :: ![Set.Set (DisjId, Int)]  -- Branches where false() was reached
  , ssIter :: !Int
  , ssHighWater :: !Int           -- Track high-water mark
  }

-- | Check if a fact's case context is in a closed branch
{-# INLINE isInClosedBranch #-}
isInClosedBranch :: Set.Set (DisjId, Int) -> [Set.Set (DisjId, Int)] -> Bool
isInClosedBranch !ancestors closedBranches =
  case closedBranches of
    [] -> False  -- Fast path: no closed branches yet
    _ -> any (`Set.isSubsetOf` ancestors) closedBranches

matchFactsToTheorem :: [Fact] -> ProofEnvironment -> [FactEntry] -> [[FactEntry]]
matchFactsToTheorem premises env newFacts =
  let !newLabels = Set.fromList (map feLabel newFacts)
   in filter (\match -> any (\fe -> Set.member (feLabel fe) newLabels) match)
             (matchPremises env premises)

autoSolve :: ProofEnvironment -> IO Bool
autoSolve = autoSolveWith defaultConfig

autoSolveWith :: SolverConfig -> ProofEnvironment -> IO Bool
autoSolveWith cfg env0 = do
  (success, _, _) <- autoSolveWithStats cfg env0
  pure success

solveWithStatsPure :: SolverConfig -> ProofEnvironment -> (SearchStatus, SolverStats, ProofEnvironment)
solveWithStatsPure cfg env0 =
  let initialQueue = Seq.fromList (peFacts env0)
      initialState =
        SearchState
          { ssEnv = env0
          , ssQueue = initialQueue
          , ssProcessed = IntSet.empty
          , ssClosedBranches = []
          , ssIter = 0
          , ssHighWater = Seq.length initialQueue
          }
      (finalSt, status) = runSearch initialState
      finalEnv = ssEnv finalSt
      stats = SolverStats
        { ssIterations = ssIter finalSt
        , ssQueueHighWater = ssHighWater finalSt
        , ssFinalQueueLen = Seq.length (ssQueue finalSt)
        , ssFinalEnvStats = getEnvStats finalEnv
        }
   in (status, stats, finalEnv)
  where
    runSearch :: SearchState -> (SearchState, SearchStatus)
    runSearch st =
      case stepSearch st of
        Left status -> (st, status)
        Right st' -> runSearch st'

    stepSearch :: SearchState -> Either SearchStatus SearchState
    stepSearch st
      | peGoalAchieved env = Left GoalFound
      | ssIter st >= scMaxIterations cfg = Left IterationLimitReached
      | Seq.null queue = Left QueueExhausted
      | otherwise =
          let (batch, restQueue) = Seq.splitAt (scBatchSize cfg) queue
              closedBranches = ssClosedBranches st
              factsToProcess =
                [ (fact, feLabel fact)
                | fact <- toList batch
                , let FactId fid = feLabel fact
                , IntSet.notMember fid processed
                , not (isInClosedBranch (feDisAncestors fact) closedBranches)
                ]
           in if null factsToProcess
                then Right st {ssQueue = restQueue, ssIter = ssIter st + 1}
                else
                  let (env', newFactsAll, newProcessedIds) = processBatch env factsToProcess
                      newClosedBranches =
                        [ feDisAncestors fe
                        | fe <- newFactsAll
                        , factName (feFact fe) == PFalse
                        ]
                      closedBranches' = newClosedBranches ++ closedBranches
                      filteredFacts =
                        [ fe
                        | fe <- newFactsAll
                        , not (isInClosedBranch (feDisAncestors fe) closedBranches')
                        ]
                      processed' = IntSet.union processed (IntSet.fromList newProcessedIds)
                      newQueue = restQueue <> Seq.fromList filteredFacts
                      newQueueLen = Seq.length newQueue
                      newHighWater = max (ssHighWater st) newQueueLen
                   in Right
                        SearchState
                          { ssEnv = env'
                          , ssQueue = newQueue
                          , ssProcessed = processed'
                          , ssClosedBranches = closedBranches'
                          , ssIter = ssIter st + 1
                          , ssHighWater = newHighWater
                          }
      where
        env = ssEnv st
        queue = ssQueue st
        processed = ssProcessed st

    processBatch envIn factsToProcess =
      let (env', dlNewFacts, dlProcessedIds) =
            foldl' processOneFact (envIn, DL.empty, DL.empty) factsToProcess
       in (env', DL.toList dlNewFacts, DL.toList dlProcessedIds)
      where
        processOneFact (!envAcc, !dlFacts, !dlIds) (fact, factId) =
          let triggeredMatches = findTriggeredMatches envAcc fact (peTriggerIndex envAcc)
              (envOut, newFacts) = applyMatches envAcc triggeredMatches
              FactId fid = factId
           in (envOut, dlFacts <> DL.fromList newFacts, DL.snoc dlIds fid)

    applyMatches envIn matches =
      let (env', dlFacts) = foldl' applyOne (envIn, DL.empty) matches
       in (env', DL.toList dlFacts)
      where
        applyOne (!envAcc, !dlFactsAcc) (thm, match) =
          let (newFacts, envOut) = runProofM (applyThmM thm match) envAcc
           in (envOut, dlFactsAcc <> DL.fromList newFacts)

-- | Solve with full stats output
autoSolveWithStats :: SolverConfig -> ProofEnvironment -> IO (Bool, SolverStats, ProofEnvironment)
autoSolveWithStats cfg env0 = do
  let (status, stats, finalEnv) = solveWithStatsPure cfg env0

  case scOutputMode cfg of
    OutputClassic -> mapM_ putStrLn (printRelevantFacts finalEnv)
    OutputClean -> mapM_ putStrLn (renderClean finalEnv)
    OutputTree -> mapM_ putStrLn (renderTree finalEnv)

  if scVerbose cfg
    then do
      putStrLn ""
      putStrLn $ "=== Solver Statistics ==="
      putStrLn $ "Iterations: " ++ show (ssIterations stats)
      putStrLn $ "Queue high-water mark: " ++ show (ssQueueHighWater stats)
      putStrLn $ "Final queue length: " ++ show (ssFinalQueueLen stats)
      let es = ssFinalEnvStats stats
      putStrLn $ "Facts: " ++ show (esFacts es)
      putStrLn $ "Disjunctions: " ++ show (esDisjunctions es)
      putStrLn $ "Symbols: " ++ show (esSymbols es)
    else pure ()

  if scDumpHashBuckets cfg
    then do
      putStrLn ""
      printHashBuckets finalEnv
    else pure ()

  putStrLn $ case status of
    GoalFound -> "SUCCESS"
    _ -> "FAILURE"
  pure (status == GoalFound, stats, finalEnv)

-- | Get stats from the environment
getEnvStats :: ProofEnvironment -> EnvStats
getEnvStats env =
  let genState = bsGenState (peBook env)
   in gsStats genState

-- | Print hash bucket distribution to spot skew
printHashBuckets :: ProofEnvironment -> IO ()
printHashBuckets env = do
  let factIdx = peFactIndex env
      bucketSizes = map (\(k, vs) -> (k, length vs)) (IntMap.toList factIdx)
      sortedBuckets = sortOn (negate . snd) bucketSizes
      totalFacts = sum (map snd bucketSizes)
      numBuckets = length bucketSizes
  putStrLn "=== Hash Bucket Distribution ==="
  putStrLn $ "Total facts: " ++ show totalFacts
  putStrLn $ "Number of buckets: " ++ show numBuckets
  if numBuckets > 0 then do
    let avgPerBucket = fromIntegral totalFacts / fromIntegral numBuckets :: Double
        maxBucket = maybe 0 snd (listToMaybe sortedBuckets)
    putStrLn $ "Average per bucket: " ++ show avgPerBucket
    putStrLn $ "Max bucket size: " ++ show maxBucket
    putStrLn "Top 10 buckets (hash, size):"
    mapM_ (\(h, sz) -> putStrLn $ "  " ++ show h ++ ": " ++ show sz) (take 10 sortedBuckets)
  else putStrLn "  (no buckets)"

-- | Convenience API to solve a simple-group-of-order-n goal with default settings.
solveOrder :: Int -> IO Bool
solveOrder n = do
  let facts = [group (sym "G"), order (sym "G") (num n), simple (sym "G")]
      goal = falseFact
      env = initEnv facts thmList thmNames goal
  autoSolve env
