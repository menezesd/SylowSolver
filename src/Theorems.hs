module Theorems
  ( thmList
  , thmNames
  ) where

import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Theorems.Counting
import Theorems.Normalizer
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
thmNames =
  Map.fromList
    [ ("sylow", sylowTheorem)
    , ("not_simple", singleSylowNotSimple)
    , ("simple_not_simple", simpleNotSimple)
    , ("alternating_order", alternatingOrder)
    , ("embed_An", embedInAn)
    , ("lagrange", lagrange)
    , ("divides_contradiction", dividesContradiction)
    , ("alternating_simple", alternatingSimple)
    , ("subgroup_index", subgroupIndex)
    , ("coset_action", cosetAction)
    , ("simple_group_action", simpleGroupAction)
    , ("count_order_pk_elements", countOrderPkElements)
    , ("counting_cont", countingContradiction)
    , ("multiple_sylows", multipleSylows)
    , ("possible_max_intersections", possibleMaxIntersections)
    , ("intersection_of_sylows", intersectionOfSylows)
    , ("normalizer_sylow_intersection", normalizerSylowIntersection)
    , ("normalizer_everything_implies_normal", normalizerEverythingImpliesNormal)
    , ("normal_subgroup_to_not_simple", normalSubgroupToNotSimple)
    , ("rule_out_max_intersections", ruleOutMaxIntersections)
    , ("rule_out_normalizer_of_intersection_order", ruleOutNormalizerOfIntersectionOrder)
    ]
