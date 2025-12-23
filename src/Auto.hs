module Auto
  ( autoSolve
  , matchFactsToTheorem
  ) where

import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Env
import EnvPrint (printRelevantFacts)

matchFactsToTheorem :: [Fact] -> [FactEntry] -> [FactEntry] -> [[FactEntry]]
matchFactsToTheorem thmFacts facts newFacts =
  let newLabels = Set.fromList [feLabel f | f <- newFacts]
      curMatches = [[]]
      dicts = [Map.empty]
      usesNewList = [False]
      step (matches, dictList, usesList) template =
        let expanded =
              [ (m ++ [f], d', uses || Set.member (feLabel f) newLabels)
              | (m, d, uses) <- zip3 matches dictList usesList
              , (f, d') <- matchFactsToTemplate template facts d
              ]
         in (map (\(a, _, _) -> a) expanded, map (\(_, b, _) -> b) expanded, map (\(_, _, c) -> c) expanded)
      (finalMatches, _, finalUses) =
        foldl step (curMatches, dicts, usesNewList) thmFacts
   in [m | (m, usesNew) <- zip finalMatches finalUses, usesNew]

matchFactsToTemplate :: Fact -> [FactEntry] -> Map String String -> [(FactEntry, Map String String)]
matchFactsToTemplate template facts initMap =
  [ (factEntry, matchMap)
  | factEntry <- facts
  , let fact = feFact factEntry
  , factName fact == factName template
  , length (factArgs fact) == length (factArgs template)
  , Just matchMap <- [matchArgs initMap (zip (factArgs template) (factArgs fact))]
  ]
  where
    matchArgs m [] = Just m
    matchArgs m ((tArg, fArg) : rest)
      | otherwise =
          case tArg of
            Exact name ->
              if name == argText fArg then matchArgs m rest else Nothing
            Var name ->
              case Map.lookup name m of
                Nothing -> matchArgs (Map.insert name (argText fArg) m) rest
                Just v -> if v == argText fArg then matchArgs m rest else Nothing
            Sym name ->
              if name == argText fArg then matchArgs m rest else Nothing
            Fresh name ->
              case Map.lookup name m of
                Nothing -> matchArgs (Map.insert name (argText fArg) m) rest
                Just v -> if v == argText fArg then matchArgs m rest else Nothing

autoSolve :: ProofEnvironment -> IO Bool
autoSolve env0 = loop env0 initialMatches 0
  where
    maxIterations = 1000
    initialMatches =
      [ (thm, matchFactsToTheorem (thmFacts thm) (peFacts env0) (peFacts env0))
      | thm <- peTheorems env0
      ]
    loop env matches iter
      | iter >= maxIterations = do
          printRelevantFacts env
          putStrLn "FAILURE"
          pure False
      | otherwise = do
          let (env', newFacts, encountered) = applyAll env matches
          if not encountered
            then do
              printRelevantFacts env'
              putStrLn "FAILURE"
              pure False
            else
              if peGoalAchieved env'
                then do
                  printRelevantFacts env'
                  putStrLn "SUCCESS"
                  pure True
                else do
                  let nextMatches =
                        [ (thm, matchFactsToTheorem (thmFacts thm) (peFacts env') newFacts)
                        | thm <- peTheorems env'
                        ]
                  loop env' nextMatches (iter + 1)
    applyAll env matches =
      foldl step (env, [], False) matches
      where
        step (envAcc, newFactsAcc, encountered) (thm, thmMatches) =
          let (env', newlyAdded) = foldl (applyOne thm) (envAcc, []) thmMatches
           in (env', newFactsAcc ++ newlyAdded, encountered || not (null thmMatches))
        applyOne thm (envAcc, newFactsAcc) match =
          let (env', newFacts) = applyThm envAcc thm match
           in (env', newFactsAcc ++ newFacts)
