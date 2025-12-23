module Theorems.Counting
  ( countOrderPkElements
  , countingContradiction
  , multipleSylows
  , possibleMaxIntersections
  , intersectionOfSylows
  , ruleOutMaxIntersections
  ) where

import Core
import NumberTheory
import Predicates
import Theorems.Common

ruleCountOrderPkElements :: [Fact] -> [Conclusion]
ruleCountOrderPkElements [factSylow, factNum, factOrder] =
  case (arg3 factSylow, arg3 factNum, arg2 factOrder) of
    (Just (_pSub, pArg, gArg), Just (_pArg2, _gArg2, nPArg), Just (_pArg3, pkArg)) ->
      let g = argText gArg
          p = readInt (argText pArg)
          nP = readInt (argText nPArg)
          pk = readInt (argText pkArg)
          lowerBound
            | pk == p = (p - 1) * nP
            | nP == 1 = pk - 1
            | otherwise = pk
       in [CFact (orderPkLowerBound (sym g) (sym (show p)) (sym (show lowerBound)))]
    _ -> []
ruleCountOrderPkElements _ = []

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
ruleCountingContradiction [fact1, fact2, factOrder] =
  case (arg3 fact1, arg3 fact2, arg2 factOrder) of
    (Just (_g1, p1Arg, n1Arg), Just (_g2, p2Arg, n2Arg), Just (_g3, nArg)) ->
      let p1 = readInt (argText p1Arg)
          p2 = readInt (argText p2Arg)
          n1 = readInt (argText n1Arg)
          n2 = readInt (argText n2Arg)
          n = readInt (argText nArg)
       in if p1 == p2
            then []
            else if n1 + n2 + 1 > n
              then [CFact falseFact]
              else []
    _ -> []
ruleCountingContradiction _ = []

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
ruleMultipleSylows [factNum] =
  case arg3 factNum of
    Just (pArg, gArg, nPArg) ->
      let nP = readInt (argText nPArg)
          p = argText pArg
          g = argText gArg
       in if nP > 1 then [CFact (moreThanOneSylow (sym p) (sym g))] else []
    _ -> []
ruleMultipleSylows _ = []

multipleSylows :: Thm
multipleSylows =
  Hyper
    ( HyperTheorem
        "multiple_sylows"
        [numSylowFact (var "p") (var "G") (var "n_p")]
        ruleMultipleSylows
    )

rulePossibleMaxIntersections :: [Fact] -> [Conclusion]
rulePossibleMaxIntersections [factMore, factOrder] =
  case (arg2 factMore, arg3 factOrder) of
    (Just (pArg, gArg), Just (_gArg2, _pArg2, pkArg)) ->
      let p = readInt (argText pArg)
          pk = readInt (argText pkArg)
          g = argText gArg
          build v
            | v == pk = []
            | otherwise = maxSylowIntersection (sym g) (sym (show p)) (sym (show v)) : build (v * p)
          disFacts = build 1
       in [CDisj (Disjunction disFacts)]
    _ -> []
rulePossibleMaxIntersections _ = []

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

ruleRuleOutMaxIntersections :: [Fact] -> [Conclusion]
ruleRuleOutMaxIntersections [factNum, factMax, factOrder] =
  case (arg3 factNum, arg3 factMax, arg3 factOrder) of
    (Just (_pArg, _gArg, npArg), Just (_gArg2, _pArg2, plArg), Just (_gArg3, _pArg3, pkArg)) ->
      let np = readInt (argText npArg)
          pl = readInt (argText plArg)
          pk = readInt (argText pkArg)
          denom = if pl == 0 then 0 else pk `div` pl
       in if denom == 0 || np `mod` denom /= 1 then [CFact falseFact] else []
    _ -> []
ruleRuleOutMaxIntersections _ = []

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
