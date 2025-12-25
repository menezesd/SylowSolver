module Theorems.Normalizer
  ( normalizerSylowIntersection
  , normalizerEverythingImpliesNormal
  , normalSubgroupToNotSimple
  , ruleOutNormalizerOfIntersectionOrder
  ) where

import Core
import Memoization (divisorsMemo, numSylowMemo)
import Predicates
import Theorems.Common (arg2, arg3)

ruleNormalizerSylowIntersection :: [Fact] -> [Conclusion]
ruleNormalizerSylowIntersection [f1, f2, f3, f4, f5, f6] =
  case (arg3 f1, arg3 f2, arg3 f3, arg2 f4, arg3 f5, arg2 f6) of
    (Just (_p1, pArg, gArg), Just (_q1, _pArg2, _gArg2), Just (_pArg3, _qArg2, rArg), Just (_rArg2, plArg), Just (_gArg3, _pArg4, pkArg), Just (_gArg4, nArg)) ->
      case (plArg, pkArg, pArg, nArg) of
        (Num pl, Num pk, Num p, Num n) ->
          let g = argText gArg
              r = argText rArg
           in if pk == pl * p
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
                      extra =
                        if null possible
                          then []
                          else [CDisj (Disjunction possible)]
                   in base ++ extra
                else []
        _ -> [] -- Not Num args
    _ -> []
ruleNormalizerSylowIntersection _ = []

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
ruleNormalSubgroupToNotSimple [factNorm, factH, factG] =
  case (arg2 factNorm, arg2 factH, arg2 factG) of
    (Just (_hArg, gArg), Just (_hArg2, hArg), Just (_gArg2, gArg2)) ->
      case (hArg, gArg2) of
        (Num h, Num g) ->
          let groupName = argText gArg
           in if h > 1 && h < g then [CFact (notSimple (sym groupName))] else []
        _ -> [] -- Not Num args
    _ -> []
ruleNormalSubgroupToNotSimple _ = []

normalSubgroupToNotSimple :: Thm
normalSubgroupToNotSimple =
  Hyper
    ( HyperTheorem
        "normal_subgroup_to_not_simple"
        [normal (var "H") (var "G"), order (var "H") (var "h"), order (var "G") (var "g")]
        ruleNormalSubgroupToNotSimple
    )

ruleRuleOutNormalizerOfIntersectionOrder :: [Fact] -> [Conclusion]
ruleRuleOutNormalizerOfIntersectionOrder [factNorm, factOrder] =
  case (arg3 factNorm, arg2 factOrder) of
    (Just (pArg, _gArg, _tArg), Just (_tArg2, kArg)) ->
      case (pArg, kArg) of
        (Num p, Num k) ->
          let nps = numSylowMemo p k
           in if length nps == 1 then [CFact falseFact] else []
        _ -> [] -- Not Num args
    _ -> []

ruleOutNormalizerOfIntersectionOrder :: Thm
ruleOutNormalizerOfIntersectionOrder =
  Hyper
    ( HyperTheorem
        "rule_out_normalizer_of_intersection_order"
        [normalizerOfSylowIntersection (var "p") (var "G") (var "T"), order (var "T") (var "k")]
        ruleRuleOutNormalizerOfIntersectionOrder
    )

