module Theorems
  ( thmList
  , thmNames
  ) where

import Core
import Data.List (foldl')
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import NumberTheory
import Predicates
import Text.Read (readMaybe)

readInt :: String -> Int
readInt s = maybe 0 id (readMaybe s)

argAt :: Fact -> Int -> String
argAt fact idx = argText (factArgs fact !! idx)

ruleSylow :: [Fact] -> [Conclusion]
ruleSylow facts =
  let groupName = argAt (facts !! 0) 0
      groupOrder = readInt (argAt (facts !! 1) 1)
      buildForP p =
        let pk = p ^ maxPDivisor groupOrder p
            base =
              [ CFact (sylowPOrder (sym groupName) (sym (show p)) (sym (show pk)))
              , CFact (sylowPSubgroup (fresh (show p)) (sym (show p)) (sym groupName))
              , CFact (order (fresh (show p)) (sym (show pk)))
              ]
            nps = numSylow p groupOrder
            disFacts =
              [ numSylowFact (sym (show p)) (sym groupName) (sym (show n))
              | n <- nps
              ]
         in if length disFacts == 1
              then base ++ map CFact disFacts
              else base ++ [CDisj (Disjunction disFacts)]
   in concatMap buildForP (primeFactors groupOrder)

sylowTheorem :: Thm
sylowTheorem =
  Hyper
    ( HyperTheorem
        "sylow"
        [group (var "G"), order (var "G") (var "n")]
        ruleSylow
    )

ruleSingleSylowNotSimple :: [Fact] -> [Conclusion]
ruleSingleSylowNotSimple facts =
  let g = argAt (facts !! 0) 2
      p = readInt (argAt (facts !! 0) 1)
      n0 = readInt (argAt (facts !! 2) 1)
      pPower = isPowerOfP n0 p
   in if n0 == 0 || pPower then [] else [CFact (notSimple (sym g))]
  where
    isPowerOfP n p'
      | n == 1 = True
      | n <= 0 = False
      | n `mod` p' /= 0 = False
      | otherwise = isPowerOfP (n `div` p') p'

singleSylowNotSimple :: Thm
singleSylowNotSimple =
  Hyper
    ( HyperTheorem
        "single_sylow_normal"
        [ sylowPSubgroup (var "H") (var "p") (var "G")
        , numSylowFact (var "p") (var "G") (exact "1")
        , order (var "G") (var "n")
        ]
        ruleSingleSylowNotSimple
    )

simpleNotSimple :: Thm
simpleNotSimple =
  Std
    (Theorem "not_simple" [simple (var "G"), notSimple (var "G")] [falseFact])

ruleEmbedInAn :: [Fact] -> [Conclusion]
ruleEmbedInAn facts =
  let nP = readInt (argAt (facts !! 0) 2)
      g = argAt (facts !! 0) 1
   in if nP > 1
        then
          [ CFact (subgroup (sym g) (fresh "alt"))
          , CFact (alternatingGroup (fresh "alt") (sym (show nP)))
          ]
        else []

embedInAn :: Thm
embedInAn =
  Hyper
    ( HyperTheorem
        "embed_An"
        [numSylowFact (var "p") (var "G") (var "n_p"), simple (var "G")]
        ruleEmbedInAn
    )

ruleAlternatingOrder :: [Fact] -> [Conclusion]
ruleAlternatingOrder facts =
  let a = argAt (facts !! 0) 0
      n = readInt (argAt (facts !! 0) 1)
      factorial m = foldl' (*) 1 [1 .. fromIntegral m]
      orderVal
        | n > 1000 = 0
        | n == 1 = 1
        | otherwise = fromIntegral (factorial n `div` 2)
   in if n > 1000 then [] else [CFact (order (sym a) (sym (show orderVal)))]

alternatingOrder :: Thm
alternatingOrder =
  Hyper
    ( HyperTheorem
        "alternating_order"
        [alternatingGroup (var "A") (var "n")]
        ruleAlternatingOrder
    )

lagrange :: Thm
lagrange =
  Std
    ( Theorem
        "lagrange"
        [subgroup (var "H") (var "G"), order (var "H") (var "n"), order (var "G") (var "m")]
        [divides (var "n") (var "m")]
    )

ruleDividesContradiction :: [Fact] -> [Conclusion]
ruleDividesContradiction facts =
  let m = readInt (argAt (facts !! 0) 0)
      n = readInt (argAt (facts !! 0) 1)
   in if n `mod` m /= 0 then [CFact falseFact] else []

dividesContradiction :: Thm
dividesContradiction =
  Hyper
    ( HyperTheorem
        "divides_contradiction"
        [divides (var "m") (var "n")]
        ruleDividesContradiction
    )

ruleAlternatingSimple :: [Fact] -> [Conclusion]
ruleAlternatingSimple facts =
  let n = readInt (argAt (facts !! 0) 1)
      a = argAt (facts !! 0) 0
   in if n >= 5 then [CFact (simple (sym a))] else []

alternatingSimple :: Thm
alternatingSimple =
  Hyper
    ( HyperTheorem
        "alternating_simple"
        [alternatingGroup (var "A") (var "n")]
        ruleAlternatingSimple
    )

ruleSubgroupIndex :: [Fact] -> [Conclusion]
ruleSubgroupIndex facts =
  let m = readInt (argAt (facts !! 1) 1)
      n = readInt (argAt (facts !! 2) 1)
      h = argAt (facts !! 0) 0
      g = argAt (facts !! 0) 1
   in if m /= 0 && n `mod` m == 0
        then [CFact (index (sym g) (sym h) (sym (show (n `div` m))))]
        else []

subgroupIndex :: Thm
subgroupIndex =
  Hyper
    ( HyperTheorem
        "subgroup_index"
        [subgroup (var "H") (var "G"), order (var "H") (var "m"), order (var "G") (var "n")]
        ruleSubgroupIndex
    )

cosetAction :: Thm
cosetAction =
  Std
    (Theorem "coset_action" [index (var "G") (var "H") (var "n")] [transitiveAction (var "G") (var "n")])

ruleSimpleGroupAction :: [Fact] -> [Conclusion]
ruleSimpleGroupAction facts =
  let n = readInt (argAt (facts !! 0) 1)
      g = argAt (facts !! 0) 0
   in if n > 1
        then
          [ CFact (subgroup (sym g) (fresh "alt"))
          , CFact (alternatingGroup (fresh "alt") (sym (show n)))
          ]
        else []

simpleGroupAction :: Thm
simpleGroupAction =
  Hyper
    ( HyperTheorem
        "simple_group_action"
        [transitiveAction (var "G") (var "n"), simple (var "G")]
        ruleSimpleGroupAction
    )

ruleCountOrderPkElements :: [Fact] -> [Conclusion]
ruleCountOrderPkElements facts =
  let g = argAt (facts !! 0) 2
      p = readInt (argAt (facts !! 0) 1)
      nP = readInt (argAt (facts !! 1) 2)
      pk = readInt (argAt (facts !! 2) 1)
      lowerBound
        | pk == p = (p - 1) * nP
        | nP == 1 = pk - 1
        | otherwise = pk
   in [CFact (orderPkLowerBound (sym g) (sym (show p)) (sym (show lowerBound)))]

countOrderPkElements :: Thm
countOrderPkElements =
  Hyper
    ( HyperTheorem
        "count_order_pk_elements"
        [ sylowPSubgroup (var "P") (var "p") (var "G")
        , numSylowFact (var "p") (var "G") (var "n_p")
        , order (var "P") (var "pk")
        ]
        ruleCountOrderPkElements
    )

ruleCountingContradiction :: [Fact] -> [Conclusion]
ruleCountingContradiction facts =
  let p1 = readInt (argAt (facts !! 0) 1)
      p2 = readInt (argAt (facts !! 1) 1)
      n1 = readInt (argAt (facts !! 0) 2)
      n2 = readInt (argAt (facts !! 1) 2)
      n = readInt (argAt (facts !! 2) 1)
   in if p1 == p2
        then []
        else if n1 + n2 + 1 > n
          then [CFact falseFact]
          else []

countingContradiction :: Thm
countingContradiction =
  Hyper
    ( HyperTheorem
        "counting_contradiction"
        [ orderPkLowerBound (var "G") (var "p1") (var "N1")
        , orderPkLowerBound (var "G") (var "p2") (var "N2")
        , order (var "G") (var "n")
        ]
        ruleCountingContradiction
    )

ruleMultipleSylows :: [Fact] -> [Conclusion]
ruleMultipleSylows facts =
  let nP = readInt (argAt (facts !! 0) 2)
      p = argAt (facts !! 0) 0
      g = argAt (facts !! 0) 1
   in if nP > 1 then [CFact (moreThanOneSylow (sym p) (sym g))] else []

multipleSylows :: Thm
multipleSylows =
  Hyper
    ( HyperTheorem
        "multiple_sylows"
        [numSylowFact (var "p") (var "G") (var "n_p")]
        ruleMultipleSylows
    )

rulePossibleMaxIntersections :: [Fact] -> [Conclusion]
rulePossibleMaxIntersections facts =
  let p = readInt (argAt (facts !! 0) 0)
      pk = readInt (argAt (facts !! 1) 2)
      g = argAt (facts !! 0) 1
      build v
        | v == pk = []
        | otherwise = maxSylowIntersection (sym g) (sym (show p)) (sym (show v)) : build (v * p)
      disFacts = build 1
   in [CDisj (Disjunction disFacts)]

possibleMaxIntersections :: Thm
possibleMaxIntersections =
  Hyper
    ( HyperTheorem
        "possible_max_intersections"
        [moreThanOneSylow (var "p") (var "G"), sylowPOrder (var "G") (var "p") (var "pk")]
        rulePossibleMaxIntersections
    )

intersectionOfSylows :: Thm
intersectionOfSylows =
  Std
    ( Theorem
        "intersection_of_sylows"
        [maxSylowIntersection (var "G") (var "p") (var "p^k")]
        [ sylowPSubgroup (fresh "P") (var "p") (var "G")
        , sylowPSubgroup (fresh "Q") (var "p") (var "G")
        , intersection (fresh "P") (fresh "Q") (fresh "R")
        , order (fresh "R") (var "p^k")
        ]
    )

ruleNormalizerSylowIntersection :: [Fact] -> [Conclusion]
ruleNormalizerSylowIntersection facts =
  let pl = readInt (argAt (facts !! 3) 1)
      pk = readInt (argAt (facts !! 4) 2)
      p = readInt (argAt (facts !! 0) 1)
      n = readInt (argAt (facts !! 5) 1)
      g = argAt (facts !! 0) 2
      r = argAt (facts !! 3) 0
   in if pk == pl * p
        then
          let base =
                [ CFact (normalizer (sym g) (sym r) (fresh "T"))
                , CFact (subgroup (fresh "T") (sym g))
                , CFact (normalizerOfSylowIntersection (sym (show p)) (sym g) (fresh "T"))
                ]
              possible =
                [ order (fresh "T") (sym (show d))
                | d <- divisors n
                , d `mod` pk == 0
                , d > pk
                ]
              extra =
                if null possible
                  then []
                  else [CDisj (Disjunction possible)]
           in base ++ extra
        else []

normalizerSylowIntersection :: Thm
normalizerSylowIntersection =
  Hyper
    ( HyperTheorem
        "normalizer_sylow_intersection"
        [ sylowPSubgroup (var "P") (var "p") (var "G")
        , sylowPSubgroup (var "Q") (var "p") (var "G")
        , intersection (var "P") (var "Q") (var "R")
        , order (var "R") (var "p^l")
        , sylowPOrder (var "G") (var "p") (var "p^k")
        , order (var "G") (var "n")
        ]
        ruleNormalizerSylowIntersection
    )

normalizerEverythingImpliesNormal :: Thm
normalizerEverythingImpliesNormal =
  Std
    ( Theorem
        "normalizer_everything_implies_normal"
        [normalizer (var "G") (var "H") (var "X"), order (var "G") (var "n"), order (var "X") (var "n")]
        [normal (var "H") (var "G")]
    )

ruleNormalSubgroupToNotSimple :: [Fact] -> [Conclusion]
ruleNormalSubgroupToNotSimple facts =
  let h = readInt (argAt (facts !! 1) 1)
      g = readInt (argAt (facts !! 2) 1)
      groupName = argAt (facts !! 0) 1
   in if h > 1 && h < g then [CFact (notSimple (sym groupName))] else []

normalSubgroupToNotSimple :: Thm
normalSubgroupToNotSimple =
  Hyper
    ( HyperTheorem
        "normal_subgroup_to_not_simple"
        [normal (var "H") (var "G"), order (var "H") (var "h"), order (var "G") (var "g")]
        ruleNormalSubgroupToNotSimple
    )

ruleRuleOutMaxIntersections :: [Fact] -> [Conclusion]
ruleRuleOutMaxIntersections facts =
  let np = readInt (argAt (facts !! 0) 2)
      pl = readInt (argAt (facts !! 1) 2)
      pk = readInt (argAt (facts !! 2) 2)
      denom = if pl == 0 then 0 else pk `div` pl
   in if denom == 0 || np `mod` denom /= 1 then [CFact falseFact] else []

ruleOutMaxIntersections :: Thm
ruleOutMaxIntersections =
  Hyper
    ( HyperTheorem
        "rule_out_max_intersections"
        [ numSylowFact (var "p") (var "G") (var "np")
        , maxSylowIntersection (var "G") (var "p") (var "p^l")
        , sylowPOrder (var "G") (var "p") (var "p^k")
        ]
        ruleRuleOutMaxIntersections
    )

ruleRuleOutNormalizerOfIntersectionOrder :: [Fact] -> [Conclusion]
ruleRuleOutNormalizerOfIntersectionOrder facts =
  let p = readInt (argAt (facts !! 0) 0)
      k = readInt (argAt (facts !! 1) 1)
      nps = numSylow p k
   in if length nps == 1 then [CFact falseFact] else []

ruleOutNormalizerOfIntersectionOrder :: Thm
ruleOutNormalizerOfIntersectionOrder =
  Hyper
    ( HyperTheorem
        "rule_out_normalizer_of_intersection_order"
        [normalizerOfSylowIntersection (var "p") (var "G") (var "T"), order (var "T") (var "k")]
        ruleRuleOutNormalizerOfIntersectionOrder
    )

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
