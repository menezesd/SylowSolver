module Environment.Goals
  ( updateGoalAchieved
  , updateUseful
  ) where

import Core
import Environment.Types
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
    observedIds = Set.map fst (Set.unions observed)

    -- Current disjunction sizes for observed disjunctions
    currentSizes :: Map.Map DisjId Int
    currentSizes =
      Map.fromList
        [ (deLabel disj, length (deFacts disj))
        | disj <- peDisjunctions env
        , Set.member (deLabel disj) observedIds
        ]

    cachedSizes = peGoalCachedDisjSizes env
    cachedCombos = peGoalCachedCombos env

    (allCombinations, envWithCache)
      | currentSizes == cachedSizes && not (null cachedCombos) = (cachedCombos, env)
      | otherwise =
          let combos = buildAllCombinations currentSizes
           in (combos, updateGoalState (\gs -> gs { gsCachedDisjSizes = currentSizes, gsCachedCombos = combos }) env)

    -- Generate all possible combinations of branches
    buildAllCombinations :: Map.Map DisjId Int -> [Set.Set (DisjId, Int)]
    buildAllCombinations sizes =
      let branchChoices =
            [ [(d, i) | i <- [0 .. size - 1]]
            | (d, size) <- Map.toList sizes
            , size > 0
            ]
       in map Set.fromList (sequence branchChoices)

    -- A combination is covered if some observed proof covers it
    isCovered :: Set.Set (DisjId, Int) -> Bool
    isCovered combo = any (`Set.isSubsetOf` combo) observed

    allCombinationsCovered = all isCovered allCombinations

-- Mark a fact and its dependencies as useful
updateUseful :: Label -> ProofEnvironment -> ProofEnvironment
updateUseful lbl env =
  case Map.lookup lbl (peFactLabels env) of
    Just (LFactEntry fe)
      | feUseful fe -> env
      | otherwise ->
          let fe' = fe {feUseful = True}
              env' = updateFactDB (\db -> db { fdFactLabels = Map.insert lbl (LFactEntry fe') (fdFactLabels db) }) env
           in foldl (flip updateUseful) env' (feDependencies fe)
    _ -> env
