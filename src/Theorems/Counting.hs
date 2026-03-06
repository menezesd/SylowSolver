module Theorems.Counting
  ( countOrderPkElements
  , countingContradiction
  , countingContradiction3
  , multipleSylows
  , possibleMaxIntersections
  , intersectionOfSylows
  , ruleOutMaxIntersections
  ) where

import Control.Monad (guard)
import Core
import Predicates
import Theorems.Common (arg2, arg3, asNum, guardList, hyper, stdThm, withArg2Num, withArg3Num)

ruleCountOrderPkElements :: [Fact] -> Maybe [Conclusion]
ruleCountOrderPkElements [factSylow, factNum, factOrder] = do
  (_pSub, pArg, gArg) <- arg3 factSylow
  p <- asNum pArg
  nP <- withArg3Num factNum (\_ _ n -> n)
  pk <- withArg2Num factOrder (\_ pkArg -> pkArg)
  let g = argText gArg
      lowerBound
        | nP == 1   = pk - 1            -- unique Sylow: all non-identity elements
        | otherwise = nP * (pk - pk `div` p)  -- elements in exactly one Sylow subgroup
  pure [CFact (orderPkLowerBound (sym g) (num p) (num lowerBound))]
ruleCountOrderPkElements _ = Nothing

countOrderPkElements :: Thm
countOrderPkElements = hyper "count_order_pk_elements"
  [ sylowPSubgroup (var "P") (var "p") (var "G")
  , numSylowFact (var "p") (var "G") (var "n_p")
  , order (var "P") (var "pk")
  ]
  ruleCountOrderPkElements

ruleCountingContradiction :: [Fact] -> Maybe [Conclusion]
ruleCountingContradiction [fact1, fact2, factOrder] = do
  (p1Arg, n1) <- withArg3Num fact1 (\_ p n -> (p, n))
  (p2Arg, n2) <- withArg3Num fact2 (\_ p n -> (p, n))
  n <- withArg2Num factOrder (\_ total -> total)
  p1 <- asNum p1Arg
  p2 <- asNum p2Arg
  guard (p1 /= p2 && n1 + n2 + 1 > n)
  pure [CFact falseFact]
ruleCountingContradiction _ = Nothing

countingContradiction :: Thm
countingContradiction = hyper "counting_contradiction"
  [ orderPkLowerBound (var "G") (var "p1") (var "N1")
  , orderPkLowerBound (var "G") (var "p2") (var "N2")
  , order (var "G") (var "n")
  ]
  ruleCountingContradiction

-- | Three-prime counting contradiction: sum element bounds for 3 distinct primes
ruleCountingContradiction3 :: [Fact] -> Maybe [Conclusion]
ruleCountingContradiction3 [fact1, fact2, fact3, factOrder] = do
  (p1Arg, n1) <- withArg3Num fact1 (\_ p n -> (p, n))
  (p2Arg, n2) <- withArg3Num fact2 (\_ p n -> (p, n))
  (p3Arg, n3) <- withArg3Num fact3 (\_ p n -> (p, n))
  n <- withArg2Num factOrder (\_ total -> total)
  p1 <- asNum p1Arg
  p2 <- asNum p2Arg
  p3 <- asNum p3Arg
  guard (p1 /= p2 && p1 /= p3 && p2 /= p3 && n1 + n2 + n3 + 1 > n)
  pure [CFact falseFact]
ruleCountingContradiction3 _ = Nothing

countingContradiction3 :: Thm
countingContradiction3 = hyper "counting_contradiction_3"
  [ orderPkLowerBound (var "G") (var "p1") (var "N1")
  , orderPkLowerBound (var "G") (var "p2") (var "N2")
  , orderPkLowerBound (var "G") (var "p3") (var "N3")
  , order (var "G") (var "n")
  ]
  ruleCountingContradiction3

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
rulePossibleMaxIntersections [factMore, factOrder] = do
  (pArg, gArg) <- arg2 factMore
  p <- asNum pArg
  pk <- withArg3Num factOrder (\_ _ pkArg -> pkArg)
  let g = argText gArg
      build v
        | v == pk = []
        | otherwise = maxSylowIntersection (sym g) (num p) (num v) : build (v * p)
      disFacts = build 1
  pure [CDisj (Disjunction disFacts)]
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
ruleRuleOutMaxIntersections [factNum, factMax, factOrder] = do
  np <- withArg3Num factNum (\_ _ npArg -> npArg)
  pl <- withArg3Num factMax (\_ _ v -> v)
  pk <- withArg3Num factOrder (\_ _ v -> v)
  let denom = if pl == 0 then 0 else pk `div` pl
  if denom == 0 || np `mod` denom /= 1
    then Just [CFact falseFact]
    else Nothing
ruleRuleOutMaxIntersections _ = Nothing

ruleOutMaxIntersections :: Thm
ruleOutMaxIntersections = hyper "rule_out_max_intersections"
  [ numSylowFact (var "p") (var "G") (var "np")
  , maxSylowIntersection (var "G") (var "p") (var "p^l")
  , sylowPOrder (var "G") (var "p") (var "p^k")
  ]
  ruleRuleOutMaxIntersections
