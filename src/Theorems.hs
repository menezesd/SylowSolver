module Theorems
  ( thmList
  , thmNames
  , buildTriggerIndex
  ) where

import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Environment.Types (TriggerIndex)
import Theorems.Counting
import Theorems.Normalizer (normalizerEverythingImpliesNormal, normalizerSylowIntersection, normalSubgroupToNotSimple, ruleOutNormalizerOfIntersectionOrder)
import Theorems.Sylow

thmList :: [Thm]
thmList =
  [ sylowTheorem
  , singleSylowNotSimple
  , simpleNotSimple
  , alternatingOrder
  , embedInAn
  , lagrange
  , dividesContradiction
  , alternatingSimple
  , subgroupIndex
  , cosetAction
  , simpleGroupAction
  , countOrderPkElements
  , countingContradiction
  , multipleSylows
  , possibleMaxIntersections
  , intersectionOfSylows
  , normalizerSylowIntersection
  , normalizerEverythingImpliesNormal
  , normalSubgroupToNotSimple
  , ruleOutMaxIntersections
  , ruleOutNormalizerOfIntersectionOrder
  ]

thmNames :: Map String Thm
thmNames = Map.fromList [(thmName thm, thm) | thm <- thmList]

-- Build trigger index for incremental theorem matching
buildTriggerIndex :: [Thm] -> TriggerIndex
buildTriggerIndex thms =
  let triggers = [ (factKey premise, TheoremTrigger thm i premises)
                 | thm <- thms
                 , let premises = thmFacts thm
                 , (i, premise) <- zip [0..] premises
                 ]
   in Map.fromListWith (++) [(k, [t]) | (k, t) <- triggers]
