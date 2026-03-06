{-# LANGUAGE BangPatterns #-}

module Environment.Goals
  ( updateGoalAchieved
  , updateUseful
  ) where

import Core
import Environment.Types
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | Update goal achieved status based on disjunction coverage.
-- The goal is achieved when all possible combinations of disjunction
-- branches have been proven (case analysis complete).
updateGoalAchieved :: ProofEnvironment -> ProofEnvironment
updateGoalAchieved env
  | null observed = env
  | allCombinationsCovered = updateGoalState (\gs -> gs { gsAchieved = True }) envWithCache
  | otherwise = envWithCache
  where
    observed = peGoalDisCombos env
    observedIds = Set.fromList [d | s <- observed, (d, _) <- Set.toList s]

    -- Bind disjunctions once to avoid redundant field access
    disjunctions = peDisjunctions env

    -- Current disjunction sizes for observed disjunctions, keyed by DisjId
    currentSizes :: Map.Map DisjId Int
    currentSizes =
      Map.fromList
        [ (deLabel disj, length (deFacts disj))
        | disj <- disjunctions
        , Set.member (deLabel disj) observedIds
        ]

    cachedSizes = peGoalCachedDisjSizes env
    cachedCombos = peGoalCachedCombos env

    (allCombinations, envWithCache)
      | currentSizes == cachedSizes && not (Set.null cachedCombos) = (cachedCombos, env)
      | otherwise =
          let combos = buildAllCombinations currentSizes
           in (combos, updateGoalState (\gs -> gs { gsCachedDisjSizes = currentSizes, gsCachedCombos = combos }) env)

    -- Generate all possible combinations of branches
    buildAllCombinations :: Map.Map DisjId Int -> Set.Set (Set.Set (DisjId, Int))
    buildAllCombinations sizes =
      let branchChoices =
            [ [(d, i) | i <- [0 .. size - 1]]
            | (d, size) <- Map.toList sizes
            , size > 0
            ]
       in Set.fromList (map Set.fromList (sequence branchChoices))

    -- A combination is covered if some observed proof covers it
    isCovered :: Set.Set (DisjId, Int) -> Bool
    isCovered combo = any (`Set.isSubsetOf` combo) observed

    allCombinationsCovered = all isCovered (Set.toList allCombinations)

-- Mark a fact and its dependencies as useful
updateUseful :: Label -> ProofEnvironment -> ProofEnvironment
updateUseful lbl env =
  let toMark = collectUseful Set.empty [lbl] env
   in if Set.null toMark
        then env
        else updateFactDB (\db -> db { fdFactLabels = markAllUseful toMark (fdFactLabels db) }) env
  where
    -- Collect all labels that need to be marked (breadth-first to avoid deep recursion)
    collectUseful !visited [] _ = visited
    collectUseful !visited (l:ls) e =
      if Set.member l visited
        then collectUseful visited ls e
        else case HashMap.lookup l (peFactLabels e) of
          Just (LFactEntry fe)
            | feUseful fe -> collectUseful visited ls e
            | otherwise -> collectUseful (Set.insert l visited) (ls ++ feDependencies fe) e
          _ -> collectUseful visited ls e

    -- Batch update: mark all facts in the set as useful
    markAllUseful toMark labels =
      HashMap.map updateIfNeeded labels
      where
        updateIfNeeded (LFactEntry fe) | Set.member (LFact (feLabel fe)) toMark =
          LFactEntry (fe {feUseful = True})
        updateIfNeeded other = other
