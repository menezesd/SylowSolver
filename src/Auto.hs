module Auto
  ( autoSolve
  , matchFactsToTheorem
  ) where

import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Sequence (Seq, ViewL(..), (|>))
import qualified Data.Sequence as Seq
import Data.Foldable (toList)
import Data.List (foldl')
import Env
import EnvPrint (printRelevantFacts)
import Unification
import IncrementalMatching (findTriggeredMatches)

matchFactsToTheorem :: [Fact] -> ProofEnvironment -> [FactEntry] -> [[FactEntry]]
matchFactsToTheorem thmFacts env newFacts =
  let facts = peFacts env -- Access all facts from the environment
      newLabels = Set.fromList [feLabel f | f <- newFacts]
      curMatches = [[]]
      dicts = [Map.empty]
      usesNewList = [False]
      step (matches, dictList, usesList) template =
        let expanded =
              [ (m ++ [f], d', uses || Set.member (feLabel f) newLabels)
              | (m, d, uses) <- zip3 matches dictList usesList
              , (f, d') <- matchFactsToTemplate template env d
              ]
         in (map (\(a, _, _) -> a) expanded, map (\(_, b, _) -> b) expanded, map (\(_, _, c) -> c) expanded)
      (finalMatches, _, finalUses) =
        foldl' step (curMatches, dicts, usesNewList) thmFacts  -- Use strict foldl'
   in [m | (m, usesNew) <- zip finalMatches finalUses, usesNew]

matchFactsToTemplate :: Fact -> ProofEnvironment -> Substitution -> [(FactEntry, Substitution)]
matchFactsToTemplate template env initMap =
  let candidateFacts =
        Map.findWithDefault [] (factKey template) (peFactIndex env)
   in [ (factEntry, matchMap)
      | factEntry <- candidateFacts
      , let fact = feFact factEntry
      , Right matchMap <- [unifyFact initMap template fact]
      ]

autoSolve :: ProofEnvironment -> IO Bool
autoSolve env0 = loop env0 (Seq.fromList (peFacts env0)) Set.empty 0
  where
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
    processBatch env factsToProcess processedSet =
      foldl' processOneFact (env, [], []) factsToProcess
      where
        processOneFact (envAcc, allNewFacts, processedIds) (fact, factId) =
          let triggeredMatches = findTriggeredMatches envAcc fact (peTriggerIndex envAcc)
              (env', newFacts) = applyMatches envAcc triggeredMatches
           in (env', allNewFacts ++ newFacts, factId : processedIds)

    -- Apply a list of (theorem, match) pairs with strict fold
    applyMatches env matches =
      foldl' applyOne (env, []) matches
      where
        applyOne (envAcc, newFactsAcc) (thm, match) =
          let (env', newFacts) = applyThm envAcc thm match
           in (env', newFactsAcc ++ newFacts)
