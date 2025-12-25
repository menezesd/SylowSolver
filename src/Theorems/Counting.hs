module Theorems.Counting
  ( countOrderPkElements
  , countingContradiction
  , multipleSylows
  , possibleMaxIntersections
  , intersectionOfSylows
  , ruleOutMaxIntersections
  ) where

import Core
import Data.Maybe (fromMaybe)
import Predicates
import Theorems.Common (arg2, arg3, guardList, hyper, stdThm, withArg3Num)

ruleCountOrderPkElements :: [Fact] -> Maybe [Conclusion]
ruleCountOrderPkElements [factSylow, factNum, factOrder] =
  case (arg3 factSylow, arg3 factNum, arg2 factOrder) of
    (Just (_pSub, pArg, gArg), Just (_pArg2, _gArg2, nPArg), Just (_pArg3, pkArg)) ->
      case (pArg, nPArg, pkArg) of
        (Num p, Num nP, Num pk) ->
          let g = argText gArg
              lowerBound
                | pk == p = (p - 1) * nP
                | nP == 1 = pk - 1
                | otherwise = pk
           in Just [CFact (orderPkLowerBound (sym g) (num p) (num lowerBound))]
        _ -> Nothing -- Not Num args
    _ -> Nothing
ruleCountOrderPkElements _ = Nothing

countOrderPkElements :: Thm
countOrderPkElements = hyper "count_order_pk_elements"
  [ sylowPSubgroup (var "P") (var "p") (var "G")
  , numSylowFact (var "p") (var "G") (var "n_p")
  , order (var "P") (var "pk")
  ]
  ruleCountOrderPkElements

ruleCountingContradiction :: [Fact] -> Maybe [Conclusion]
ruleCountingContradiction [fact1, fact2, factOrder] =
  case (arg3 fact1, arg3 fact2, arg2 factOrder) of
    (Just (_, p1Arg, n1Arg), Just (_, p2Arg, n2Arg), Just (_, nArg)) ->
      case (p1Arg, p2Arg, n1Arg, n2Arg, nArg) of
        (Num p1, Num p2, Num n1, Num n2, Num n) ->
          if p1 == p2
            then Nothing
            else if n1 + n2 + 1 > n
              then Just [CFact falseFact]
              else Nothing
        _ -> Nothing -- Not Num args
    _ -> Nothing
ruleCountingContradiction _ = Nothing

countingContradiction :: Thm
countingContradiction = hyper "counting_contradiction"
  [ orderPkLowerBound (var "G") (var "p1") (var "N1")
  , orderPkLowerBound (var "G") (var "p2") (var "N2")
  , order (var "G") (var "n")
  ]
  ruleCountingContradiction

ruleMultipleSylows :: [Fact] -> Maybe [Conclusion]
ruleMultipleSylows [factNum] = do
  (pArg, gArg, nP) <- withArg3Num factNum (,,)
  let p = argText pArg
      g = argText gArg
  pure $ guardList (nP > 1) (CFact (moreThanOneSylow (sym p) (sym g)))
ruleMultipleSylows _ = Nothing

multipleSylows :: Thm
multipleSylows = hyper "multiple_sylows"
  [numSylowFact (var "p") (var "G") (var "n_p")]
  ruleMultipleSylows

rulePossibleMaxIntersections :: [Fact] -> Maybe [Conclusion]
rulePossibleMaxIntersections [factMore, factOrder] =
  case (arg2 factMore, arg3 factOrder) of
    (Just (pArg, gArg), Just (_gArg2, _pArg2, pkArg)) ->
      case (pArg, pkArg) of
        (Num p, Num pk) ->
          let g = argText gArg
              build v
                | v == pk = []
                | otherwise = maxSylowIntersection (sym g) (num p) (num v) : build (v * p)
              disFacts = build 1
           in Just [CDisj (Disjunction disFacts)]
        _ -> Nothing -- Not Num args
    _ -> Nothing
rulePossibleMaxIntersections _ = Nothing

possibleMaxIntersections :: Thm
possibleMaxIntersections = hyper "possible_max_intersections"
  [moreThanOneSylow (var "p") (var "G"), sylowPOrder (var "G") (var "p") (var "pk")]
  rulePossibleMaxIntersections

intersectionOfSylows :: Thm
intersectionOfSylows = stdThm "intersection_of_sylows"
  [maxSylowIntersection (var "G") (var "p") (var "p^k")]
  [ sylowPSubgroup (fresh "P") (var "p") (var "G")
  , sylowPSubgroup (fresh "Q") (var "p") (var "G")
  , intersection (fresh "P") (fresh "Q") (fresh "R")
  , order (fresh "R") (var "p^k")
  ]

ruleRuleOutMaxIntersections :: [Fact] -> Maybe [Conclusion]
ruleRuleOutMaxIntersections [factNum, factMax, factOrder] =
  case (arg3 factNum, arg3 factMax, arg3 factOrder) of
    (Just (_pArg, _gArg, npArg), Just (_gArg2, _pArg2, plArg), Just (_gArg3, _pArg3, pkArg)) ->
      case (npArg, plArg, pkArg) of
        (Num np, Num pl, Num pk) ->
          let denom = if pl == 0 then 0 else pk `div` pl
           in if denom == 0 || np `mod` denom /= 1 then Just [CFact falseFact] else Nothing
        _ -> Nothing -- Not Num args
    _ -> Nothing
ruleRuleOutMaxIntersections _ = Nothing

ruleOutMaxIntersections :: Thm
ruleOutMaxIntersections = hyper "rule_out_max_intersections"
  [ numSylowFact (var "p") (var "G") (var "np")
  , maxSylowIntersection (var "G") (var "p") (var "p^l")
  , sylowPOrder (var "G") (var "p") (var "p^k")
  ]
  ruleRuleOutMaxIntersections
