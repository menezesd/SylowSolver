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
  ( autoSolve
  , matchFactsToTheorem
  ) where

-- Standard library
import Data.Foldable (toList)
import Data.List (foldl')
import Data.Sequence ((|>))
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

-- Local modules
import Core
import Env
import Environment.Types (peFacts, peGoalAchieved)
import EnvPrint (printRelevantFacts)
import IncrementalMatching (findTriggeredMatches, matchFactsToTemplate)
import ProofMonad (runProofM)
import Environment.FactsMonadic (applyThmM)

matchFactsToTheorem :: [Fact] -> ProofEnvironment -> [FactEntry] -> [[FactEntry]]
matchFactsToTheorem premises env newFacts =
  let newLabels = Set.fromList [feLabel f | f <- newFacts]
      curMatches = [[]]
      dicts = [Map.empty]
      usesNewList = [False]
      step (matches, dictList, usesList) template =
        let expanded =
              [ (m ++ [f], d', uses || Set.member (feLabel f) newLabels)
              | (m, d, uses) <- zip3 matches dictList usesList
              , (f, d') <- matchFactsToTemplate template env d
              ]
         in unzip3 expanded
      (finalMatches, _, finalUses) =
        foldl' step (curMatches, dicts, usesNewList) premises  -- Use strict foldl'
   in [m | (m, usesNew) <- zip finalMatches finalUses, usesNew]

autoSolve :: ProofEnvironment -> IO Bool
autoSolve env0 = loop env0 (Seq.fromList (peFacts env0)) Set.empty (0 :: Int)
  where
    maxIterations :: Int
    maxIterations = 1000
    batchSize = 8  -- Process facts in small batches to reduce loop overhead

    -- Agenda-based loop: process facts in batches from the work queue
    loop env workQueue processedSet iter
      | iter >= maxIterations = do
          mapM_ putStrLn (printRelevantFacts env)
          putStrLn "FAILURE"
          pure False
      | Seq.null workQueue = do
          -- Queue exhausted: check if we achieved the goal
          if peGoalAchieved env
            then do
              mapM_ putStrLn (printRelevantFacts env)
              putStrLn "SUCCESS"
              pure True
            else do
              mapM_ putStrLn (printRelevantFacts env)
              putStrLn "FAILURE"
              pure False
      | peGoalAchieved env = do
          -- Goal achieved: stop immediately
          mapM_ putStrLn (printRelevantFacts env)
          putStrLn "SUCCESS"
          pure True
      | otherwise = do
          -- Extract a batch of facts to process
          let (batch, restQueue) = Seq.splitAt batchSize workQueue
              factsToProcess = [(fact, feLabel fact) | fact <- toList batch, Set.notMember (feLabel fact) processedSet]

          if null factsToProcess
            then loop env restQueue processedSet iter  -- All facts in batch already processed
            else do
              -- Process all facts in the batch
              let (env', newFactsAll, newProcessedIds) = processBatch env factsToProcess processedSet
                  processedSet' = foldl' (flip Set.insert) processedSet newProcessedIds
                  -- Add new facts to the work queue - O(k) amortized with Seq
                  newQueue = foldl' (|>) restQueue newFactsAll

              loop env' newQueue processedSet' (iter + 1)

    -- Process a batch of facts
    -- Accumulates facts in reverse order, then reverses at the end
    processBatch env factsToProcess _processedSet =
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
