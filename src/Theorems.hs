module Theorems
  ( thmList
  , thmNames
  ) where

import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
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
