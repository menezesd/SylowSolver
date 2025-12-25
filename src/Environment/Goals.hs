module Environment.Goals
  ( updateGoalAchieved
  , updateUseful
  , factEquals
  ) where

import Core
import Environment.Types
import Environment.Accessors
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- Check if two facts are equal (same name and args)
factEquals :: Fact -> Fact -> Bool
factEquals a b = factName a == factName b && factArgs a == factArgs b

-- Update goal achieved status based on disjunction coverage
updateGoalAchieved :: ProofEnvironment -> ProofEnvironment
updateGoalAchieved env =
  if null (peGoalDisCombos env)
    then env
    else
      let fullDisSet = Set.unions (peGoalDisCombos env)
          disLabels = Set.toList (Set.map fst fullDisSet)
          disSizes =
            [ (d, length facts)
            | d <- disLabels
            , Just (LDisjEntry disj) <- [Map.lookup (LDisj d) (peFactLabels env)]
            , let facts = deFacts disj
            ]
          cartesian [] = [[]]
          cartesian (xs : xss) = [x : ys | x <- xs, ys <- cartesian xss]
          domain =
            [ [ (d, i) | i <- [0 .. l - 1] ]
            | (d, l) <- disSizes
            ]
          fullCombos = map Set.fromList (cartesian domain)
          observed = peGoalDisCombos env
          covered s = any (`Set.isSubsetOf` s) observed
          allCovered = all covered fullCombos
       in if allCovered
          then updateGoalState (\gs -> gs { gsAchieved = True }) env
          else env

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
