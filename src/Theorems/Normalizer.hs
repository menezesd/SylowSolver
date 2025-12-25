module Theorems.Normalizer
  ( normalizerSylowIntersection
  , normalizerEverythingImpliesNormal
  , normalSubgroupToNotSimple
  , ruleOutNormalizerOfIntersectionOrder
  ) where

import Core
import Memoization (divisorsMemo, numSylowMemo)
import Predicates
import Theorems.Common (arg2, arg3, asNum, hyper, stdThm)

ruleNormalizerSylowIntersection :: [Fact] -> Maybe [Conclusion]
ruleNormalizerSylowIntersection [f1, _f2, f3, f4, f5, f6] = do
  (_p1, pArg, gArg) <- arg3 f1
  (_pArg3, _qArg2, rArg) <- arg3 f3
  (_rArg2, plArg) <- arg2 f4
  (_gArg3, _pArg4, pkArg) <- arg3 f5
  (_gArg4, nArg) <- arg2 f6
  pl <- asNum plArg
  pk <- asNum pkArg
  p <- asNum pArg
  n <- asNum nArg
  let g = argText gArg
      r = argText rArg
  if pk == pl * p
    then
      let base =
            [ CFact (normalizer (sym g) (sym r) (fresh "T"))
            , CFact (subgroup (fresh "T") (sym g))
            , CFact (normalizerOfSylowIntersection (num p) (sym g) (fresh "T"))
            ]
          possible =
            [ order (fresh "T") (num d)
            | d <- divisorsMemo n
            , d `mod` pk == 0
            , d > pk
            ]
          extra = if null possible then [] else [CDisj (Disjunction possible)]
       in Just (base ++ extra)
    else Nothing
ruleNormalizerSylowIntersection _ = Nothing

normalizerSylowIntersection :: Thm
normalizerSylowIntersection = hyper "normalizer_sylow_intersection"
  [ sylowPSubgroup (var "P") (var "p") (var "G")
  , sylowPSubgroup (var "Q") (var "p") (var "G")
  , intersection (var "P") (var "Q") (var "R")
  , order (var "R") (var "p^l")
  , sylowPOrder (var "G") (var "p") (var "p^k")
  , order (var "G") (var "n")
  ]
  ruleNormalizerSylowIntersection

normalizerEverythingImpliesNormal :: Thm
normalizerEverythingImpliesNormal = stdThm "normalizer_everything_implies_normal"
  [normalizer (var "G") (var "H") (var "X"), order (var "G") (var "n"), order (var "X") (var "n")]
  [normal (var "H") (var "G")]

ruleNormalSubgroupToNotSimple :: [Fact] -> Maybe [Conclusion]
ruleNormalSubgroupToNotSimple [factNorm, factH, factG] = do
  (_hArg, gArg) <- arg2 factNorm
  (_hArg2, hArg) <- arg2 factH
  (_gArg2, gArg2) <- arg2 factG
  h <- asNum hArg
  g <- asNum gArg2
  let groupName = argText gArg
  if h > 1 && h < g then Just [CFact (notSimple (sym groupName))] else Nothing
ruleNormalSubgroupToNotSimple _ = Nothing

normalSubgroupToNotSimple :: Thm
normalSubgroupToNotSimple = hyper "normal_subgroup_to_not_simple"
  [normal (var "H") (var "G"), order (var "H") (var "h"), order (var "G") (var "g")]
  ruleNormalSubgroupToNotSimple

ruleRuleOutNormalizerOfIntersectionOrder :: [Fact] -> Maybe [Conclusion]
ruleRuleOutNormalizerOfIntersectionOrder [factNorm, factOrder] = do
  (pArg, _gArg, _tArg) <- arg3 factNorm
  (_tArg2, kArg) <- arg2 factOrder
  p <- asNum pArg
  k <- asNum kArg
  let nps = numSylowMemo p k
  case nps of
    [_] -> Just [CFact falseFact]
    _ -> Nothing
ruleRuleOutNormalizerOfIntersectionOrder _ = Nothing

ruleOutNormalizerOfIntersectionOrder :: Thm
ruleOutNormalizerOfIntersectionOrder = hyper "rule_out_normalizer_of_intersection_order"
  [normalizerOfSylowIntersection (var "p") (var "G") (var "T"), order (var "T") (var "k")]
  ruleRuleOutNormalizerOfIntersectionOrder
