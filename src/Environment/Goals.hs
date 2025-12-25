module Environment.Goals
  ( updateGoalAchieved
  , updateUseful
  ) where

import Core
import Environment.Types
import Environment.Types
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- | Update goal achieved status based on disjunction coverage.
-- The goal is achieved when all possible combinations of disjunction
-- branches have been proven (case analysis complete).
updateGoalAchieved :: ProofEnvironment -> ProofEnvironment
updateGoalAchieved env
  | null observed = env
  | allCombinationsCovered = updateGoalState (\gs -> gs { gsAchieved = True }) env
  | otherwise = env
  where
    observed = peGoalDisCombos env

    -- Get all disjunction IDs referenced in proofs
    allDisjIds = Set.toList $ Set.map fst $ Set.unions observed

    -- Look up disjunction size from environment
    disjSize :: DisjId -> Int
    disjSize d = case Map.lookup (LDisj d) (peFactLabels env) of
      Just (LDisjEntry disj) -> length (deFacts disj)
      _ -> 0

    -- Generate all branch indices for each disjunction
    branchChoices :: [[(DisjId, Int)]]
    branchChoices = [ [(d, i) | i <- [0 .. disjSize d - 1]] | d <- allDisjIds ]

    -- All possible combinations of branch choices (Cartesian product)
    allCombinations :: [Set.Set (DisjId, Int)]
    allCombinations = map Set.fromList (sequence branchChoices)

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
