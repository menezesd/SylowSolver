module Theorems
  ( thmList
  , thmNames
  , buildTriggerIndex
  ) where

import Core
import qualified Data.HashMap.Strict as HashMap
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

thmNames :: HashMap.HashMap TheoremName Thm
thmNames = HashMap.fromList [(thmId thm, thm) | thm <- thmList]

-- Build trigger index for incremental theorem matching
buildTriggerIndex :: [Thm] -> TriggerIndex
buildTriggerIndex thms =
  let triggers = [ (factKey premise, TheoremTrigger thm i premises)
                 | thm <- thms
                 , let premises = thmFacts thm
                 , (i, premise) <- zip [0..] premises
                 ]
   in HashMap.fromListWith (++) [(k, [t]) | (k, t) <- triggers]
