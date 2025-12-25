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
  , defaultConfig
  , autoSolve
  , autoSolveWith
  , matchFactsToTheorem
  , solveOrder
  ) where

-- Standard library
import Data.Foldable (toList)
import Data.List (foldl')
import Data.Sequence ((|>))
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

-- Local modules
import Core
import Env
import EnvPrint (printRelevantFacts)
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

data SolverConfig = SolverConfig
  { scMaxIterations :: Int
  , scBatchSize :: Int
  } deriving (Eq, Show)

defaultConfig :: SolverConfig
defaultConfig = SolverConfig { scMaxIterations = 1000, scBatchSize = 8 }

data SearchState = SearchState
  { ssEnv :: ProofEnvironment
  , ssQueue :: Seq.Seq FactEntry
  , ssProcessed :: Set.Set FactId
  , ssIter :: Int
  }

matchFactsToTheorem :: [Fact] -> ProofEnvironment -> [FactEntry] -> [[FactEntry]]
matchFactsToTheorem premises env newFacts =
  let newLabels = Set.fromList [feLabel f | f <- newFacts]
   in [ match
      | match <- matchPremises env premises
      , any (\fe -> Set.member (feLabel fe) newLabels) match
      ]

autoSolve :: ProofEnvironment -> IO Bool
autoSolve = autoSolveWith defaultConfig

autoSolveWith :: SolverConfig -> ProofEnvironment -> IO Bool
autoSolveWith cfg env0 = do
  let initialState =
        SearchState
          { ssEnv = env0
          , ssQueue = Seq.fromList (peFacts env0)
          , ssProcessed = Set.empty
          , ssIter = 0
          }
      (finalEnv, status) = runSearch initialState
  mapM_ putStrLn (printRelevantFacts finalEnv)
  putStrLn $ case status of
    GoalFound -> "SUCCESS"
    _ -> "FAILURE"
  pure (status == GoalFound)
  where
    runSearch :: SearchState -> (ProofEnvironment, SearchStatus)
    runSearch st =
      case stepSearch st of
        Left status -> (ssEnv st, status)
        Right st' -> runSearch st'

    stepSearch :: SearchState -> Either SearchStatus SearchState
    stepSearch st
      | peGoalAchieved env = Left GoalFound
      | ssIter st >= scMaxIterations cfg = Left IterationLimitReached
      | Seq.null queue = Left QueueExhausted
      | otherwise =
          let (batch, restQueue) = Seq.splitAt (scBatchSize cfg) queue
              factsToProcess = [(fact, feLabel fact) | fact <- toList batch, Set.notMember (feLabel fact) processed]
           in if null factsToProcess
                then Right st { ssQueue = restQueue, ssIter = ssIter st + 1 }
                else
                  let (env', newFactsAll, newProcessedIds) = processBatch env factsToProcess
                      processed' = foldl' (flip Set.insert) processed newProcessedIds
                      newQueue = foldl' (|>) restQueue newFactsAll
                   in Right
                        SearchState
                          { ssEnv = env'
                          , ssQueue = newQueue
                          , ssProcessed = processed'
                          , ssIter = ssIter st + 1
                          }
      where
        env = ssEnv st
        queue = ssQueue st
        processed = ssProcessed st

    -- Process a batch of facts
    -- Accumulates facts in reverse order, then reverses at the end
    processBatch env factsToProcess =
      let (env', revNewFacts, revProcessedIds) =
            foldl' processOneFact (env, [], []) factsToProcess
       in (env', reverse revNewFacts, reverse revProcessedIds)
      where
        processOneFact (!envAcc, !allNewFactsRev, !processedIdsRev) (fact, factId) =
          let triggeredMatches = findTriggeredMatches envAcc fact (peTriggerIndex envAcc)
              (env', newFacts) = applyMatches envAcc triggeredMatches
              -- Prepend new facts (will reverse at end)
           in (env', reverseOnto newFacts allNewFactsRev, factId : processedIdsRev)

    -- Apply a list of (theorem, match) pairs with strict fold
    -- Accumulates in reverse, then reverses at the end
    applyMatches env matches =
      let (env', revFacts) = foldl' applyOne (env, []) matches
       in (env', reverse revFacts)
      where
        applyOne (!envAcc, !newFactsAccRev) (thm, match) =
          let (newFacts, env') = runProofM (applyThmM thm match) envAcc
           in (env', reverseOnto newFacts newFactsAccRev)

    -- Helper: reverse xs onto ys (like reverse xs ++ ys but O(n) not O(2n))
    {-# INLINE reverseOnto #-}
    reverseOnto :: [a] -> [a] -> [a]
    reverseOnto [] !ys = ys
    reverseOnto (x:xs) !ys = reverseOnto xs (x:ys)

-- | Convenience API to solve a simple-group-of-order-n goal with default settings.
solveOrder :: Int -> IO Bool
solveOrder n = do
  let facts = [group (sym "G"), order (sym "G") (num n), simple (sym "G")]
      goal = falseFact
      env = initEnv facts thmList thmNames goal
  autoSolve env
