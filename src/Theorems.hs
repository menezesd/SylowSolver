-- | Standard theorems for the Sylow solver
module Theorems where

import Types
  ( Fact(..)
  , Pred(..)
  , Value(..)
  , TPattern(..)
  , TTemplate(..)
  , ThmOut(..)
  , Theorem(..)
  , mkFactP
  , parseSymGroup
  , parseAltGroup
  , vpFixed, vpVar, vpAny
  , mkTPattern, mkTTemplate
  , mkTheoremT
  )
import Math
import Errors

-- Sylow's theorem - generates constraints on number of Sylow p-subgroups
sylowTheorem :: Theorem
sylowTheorem = mkTheoremT "SylowDivisibilityCongruence"
  (mkTTemplate [ mkTPattern "group" [vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySylow
  where
    applySylow [_, Fact _ [_, nStr] _ _] =
      case safeRead nStr of
        Right n -> case primeFactorization n of
          Right factors -> 
            let makeConstraint (p, k) = 
                  let pk = p ^ k
                      m = n `div` pk  -- n = p^k * m, so m = n / p^k
                      -- Generate sylow_order fact (typed)
                      orderFact = TOFact (mkFactP PSylowOrder [Sym "G", Nat p, Nat pk])
                  in case allDivisors m of
                    Right divisors ->
                      let validCounts = [d | d <- divisors, d `mod` p == 1]
                          alternatives = [mkFactP PNumSylow [Nat p, Sym "G", Nat d] | d <- validCounts]
                          countConstraint = case alternatives of
                                              [] -> TOFact (mkFactP PFalse [])
                                              [single] -> TOFact single
                                              multiple -> TODisj multiple
                      in [orderFact, countConstraint]
                    Left _ -> [TOFact (mkFactP PFalse [])] -- Error case
            in concat $ map makeConstraint factors
          Left _ -> [TOFact (mkFactP PFalse [])] -- Error case
        Left _ -> [TOFact (mkFactP PFalse [])] -- Parse error case
    applySylow _ = []

-- If there's a unique Sylow p-subgroup in a simple group, contradiction
-- (only applies when the Sylow subgroup is proper)
uniqueSylowContradiction :: Theorem
uniqueSylowContradiction = mkTheoremT "UniqueSylowImpliesNotSimple"
  (mkTTemplate [ mkTPattern "simple" [vpVar "G"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpFixed (Nat 1)]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyUniqueSylow
  where
    applyUniqueSylow [_, Fact _ [pStr, _, _] _ _, Fact _ [_, p2Str, pkStr] _ _, Fact _ [_, nStr] _ _]
      | pStr == p2Str =
        case (safeRead pkStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
          (Right pk, Right n) -> 
            -- Only apply if p^k < n (proper subgroup)
            if pk < n then [TOFact (mkFactP PFalse [])] else []
          _ -> []
    applyUniqueSylow _ = []

-- Generate Sylow p-subgroup facts when needed for counting
sylowPSubgroupGeneration :: Theorem
sylowPSubgroupGeneration = mkTheoremT "SylowPSubgroupGeneration"
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               ])
  applySylowPGeneration
  where
    applySylowPGeneration [Fact _ [pStr,g,_] _ _, Fact _ [g2,p2Str,pkStr] _ _]
      | g == g2 && pStr == p2Str =
        case (safeRead pStr :: ProverResult Integer, safeRead pkStr :: ProverResult Integer) of
          (Right p, Right pk) ->
            let sylowName = "S" ++ pStr  -- Generate Sylow p-subgroup name
            in [ TOFact (mkFactP PSylowPSubgroup [Sym sylowName, Nat p, Sym g])
               , TOFact (mkFactP POrder [Sym sylowName, Nat pk])
               ]
          _ -> []
    applySylowPGeneration _ = []



-- Action on Sylow subgroups: if n_p > 1, G acts on them.
actionOnSylowSubgroups :: Theorem
actionOnSylowSubgroups = mkTheoremT "ActionOnSylowSubgroups"
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"] ])
  applyAction
  where
    applyAction [Fact _ [_,g,npStr] _ _] =
      case (safeRead npStr :: ProverResult Integer) of
        Right np -> if np > 1 
                    then [TOFact (mkFactP PTransitiveAction [Sym g, Nat np])]
                    else []
        _ -> []
    applyAction _ = []

-- Any transitive action of degree n yields a faithful embedding G ↪ S_n (encode as embedsInSym)
actionEmbedsInSym :: Theorem
actionEmbedsInSym = mkTheoremT "ActionEmbedsInSym"
  (mkTTemplate [ mkTPattern "transitiveAction" [vpVar "G", vpVar "n"] ])
  applyActionEmbeds
  where
    applyActionEmbeds [Fact _ [g, nStr] _ _] =
      case safeRead nStr of
        Right n -> [TOFact (mkFactP PEmbedsInSym [Sym g, SymGroup n])]
        _ -> []
    applyActionEmbeds _ = []

-- Order must divide symmetric group order
orderDividesSym :: Theorem
orderDividesSym = mkTheoremT "OrderMustDivideSym"
  (mkTTemplate [ mkTPattern "embedsInSym" [vpVar "G", vpVar "Sn"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySymDivision
  where
    applySymDivision [Fact _ [_, snStr] _ _, Fact _ [_, nStr] _ _] =
      case (safeRead nStr, parseSymGroup snStr) of
        (Right groupOrder, Just m) -> case factorial m of
          Right factM -> 
            if factM `mod` groupOrder /= 0 
               then [TOFact (mkFactP PFalse [])]
               else []
          Left _ -> [TOFact (mkFactP PFalse [])] -- Factorial error
        _ -> [TOFact (mkFactP PFalse [])] -- Parse error
    applySymDivision _ = []

orderDividesAlt :: Theorem
orderDividesAlt = mkTheoremT "OrderMustDivideAlt"
  (mkTTemplate [ mkTPattern "embedInAlt" [vpVar "G", vpVar "An"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyDivision
  where
    applyDivision [Fact _ [_, aStr] _ _, Fact _ [_, nStr] _ _] =
      case (parseAltGroup aStr, safeRead nStr :: ProverResult Integer) of
        (Just m, Right n) -> case factorial m of
          Right factM -> 
            let altOrder = factM `div` 2
            in if altOrder `mod` n /= 0 
               then [TOFact (mkFactP PFalse [])]
               else []
          Left _ -> [TOFact (mkFactP PFalse [])]
        _ -> [TOFact (mkFactP PFalse [])]
    applyDivision _ = []

-- Count elements of order p^k in Sylow p-subgroups (match Python pattern)
countOrderPkElements :: Theorem
countOrderPkElements = mkTheoremT "CountOrderPkElements"
  (mkTTemplate [ mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "order" [vpVar "P", vpVar "pk"]
               ])
  applyCountOrderPkElements
  where
    applyCountOrderPkElements [Fact _ [p,pStr1,g] _ _, Fact _ [pStr2,g2,npStr] _ _, Fact _ [p2,pkStr] _ _]
      | pStr1 == pStr2 && g == g2 && p == p2 =
          case (safeRead pStr1 :: ProverResult Integer, 
                safeRead npStr :: ProverResult Integer, 
                safeRead pkStr :: ProverResult Integer) of
            (Right prime, Right numSylow, Right pk) ->
              let lowerBound = if pk == prime  -- Cyclic of prime order
                              then (prime - 1) * numSylow
                              else if numSylow == 1
                                   then pk - 1
                                   else pk  -- Conservative bound for multiple Sylow subgroups
              in [TOFact (mkFactP POrderPkLowerBound [Sym g, Nat prime, Nat lowerBound])]
            _ -> []
    applyCountOrderPkElements _ = []

-- Counting contradiction: if sum of elements exceeds group order
countingContradiction :: Theorem  
countingContradiction = mkTheoremT "CountingContradiction"
  (mkTTemplate [ mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p1", vpVar "N1"]
               , mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p2", vpVar "N2"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyCountingContradiction
  where
    applyCountingContradiction [Fact _ [_,p1Str,n1Str] _ _, 
                               Fact _ [_,p2Str,n2Str] _ _, 
                               Fact _ [_,nStr] _ _] =
      case (safeRead p1Str :: ProverResult Integer, safeRead p2Str :: ProverResult Integer, 
            safeRead n1Str :: ProverResult Integer, safeRead n2Str :: ProverResult Integer, 
            safeRead nStr :: ProverResult Integer) of
        (Right p1, Right p2, Right n1, Right n2, Right n) ->
          if p1 /= p2 && n1 + n2 + 1 > n  -- +1 for identity element
          then [TOFact (mkFactP PFalse [])]
          else []
        _ -> []
    applyCountingContradiction _ = []

-- Lagrange's theorem: order of subgroup divides order of group
lagrangeTheorem :: Theorem
lagrangeTheorem = mkTheoremT "LagrangeTheorem"
  (mkTTemplate [ mkTPattern "subgroup" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyLagrange
  where
    applyLagrange [Fact _ [h,g] _ _, Fact _ [h2,mStr] _ _, Fact _ [g2,nStr] _ _]
      | h == h2 && g == g2 =
        case (safeRead mStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
          (Right m, Right n) -> [TOFact (mkFactP PDivides [Nat m, Nat n])]
          _ -> []
    applyLagrange _ = []

-- Divisibility contradiction: if m should divide n but doesn't
divisibilityContradiction :: Theorem
divisibilityContradiction = mkTheoremT "DivisibilityContradiction"
  (mkTTemplate [ mkTPattern "divides" [vpVar "m", vpVar "n"] ])
  applyDivisibilityContradiction
  where
    applyDivisibilityContradiction [Fact _ [mStr,nStr] _ _] =
         case (safeRead mStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
           (Right m, Right n) -> 
             if n `mod` m /= 0
             then [TOFact (mkFactP PFalse [])]
             else []
           _ -> []
    applyDivisibilityContradiction _ = []

-- A_n is simple for n >= 5
alternatingGroupSimple :: Theorem
alternatingGroupSimple = mkTheoremT "AlternatingGroupSimple"
  (mkTTemplate [ mkTPattern "alternatingGroup" [vpVar "A", vpVar "n"] ])
  applyAlternatingSimple
  where
    applyAlternatingSimple [Fact _ [a,nStr] _ _] =
      case (safeRead nStr :: ProverResult Integer) of
        Right n -> if n >= 5
                  then [TOFact (mkFactP PSimple [Sym a])]
                  else []
        _ -> []
    applyAlternatingSimple _ = []

-- Subgroup index theorem: |G:H| = |G| / |H|
subgroupIndex :: Theorem
subgroupIndex = mkTheoremT "SubgroupIndex"
  (mkTTemplate [ mkTPattern "subgroup" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               ])
  applySubgroupIndex
  where
    applySubgroupIndex [Fact _ [h,g] _ _, Fact _ [g2,nStr] _ _, Fact _ [h2,mStr] _ _]
      | g == g2 && h == h2 =
        case (safeRead nStr :: ProverResult Integer, safeRead mStr :: ProverResult Integer) of
          (Right n, Right m) -> 
            if m > 0 && n `mod` m == 0
            then [TOFact (mkFactP PIndex [Sym h, Sym g, Nat (n `div` m)])]
            else []
          _ -> []
    applySubgroupIndex _ = []

-- Coset action theorem: G acts transitively on cosets of H with index n
cosetAction :: Theorem
cosetAction = mkTheoremT "CosetAction"
  (mkTTemplate [ mkTPattern "index" [vpVar "H", vpVar "G", vpVar "n"] ])
  applyCosetAction
  where
    applyCosetAction [Fact _ [_,g,nStr] _ _] =
      case (safeRead nStr :: ProverResult Integer) of
        Right n -> [TOFact (mkFactP PTransitiveAction [Sym g, Nat n])]
        _ -> []
    applyCosetAction _ = []

-- Simple group action theorem: if G is simple and has n_p > 1 Sylow p-subgroups, it embeds in A_{n_p}
simpleGroupAction :: Theorem
simpleGroupAction = mkTheoremT "EmbedsIntoSnBySylowAction"
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "simple" [vpVar "G"]
               ])
  applySimpleGroupAction
  where
    applySimpleGroupAction [Fact _ [_,g,npStr] _ _, Fact _ [g2] _ _]
      | g == g2 =
           case safeRead npStr of
       (Right n) -> if n > 1 && n <= 20
              then [TOFact (mkFactP PEmbedsInSym [Sym g, SymGroup n])]
              else []
       _ -> []
    applySimpleGroupAction _ = []

-- Multiple Sylows theorem: if num_sylow(p,G,n) where n > 1, then more_than_one_sylow(p,G)
multipleSylows :: Theorem
multipleSylows = mkTheoremT "MultipleSylows"
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"] ])
  applyMultipleSylows
  where
    applyMultipleSylows [Fact _ [p,g,nStr] _ _] =
      case safeRead nStr :: ProverResult Integer of
        (Right n) -> if n > 1
                      then case (safeRead p :: ProverResult Integer) of
                             Right pInt -> [TOFact (mkFactP PMoreThanOneSylow [Nat pInt, Sym g])]
                             _ -> []
                      else []
        _ -> []
    applyMultipleSylows _ = []

-- Alternating order theorem: alternating_group(A,n) implies order(A, n!/2)
alternatingOrder :: Theorem
alternatingOrder = mkTheoremT "AlternatingOrder"
  (mkTTemplate [ mkTPattern "alternatingGroup" [vpVar "A", vpVar "n"] ])
  applyAlternatingOrder
  where
    applyAlternatingOrder [Fact _ [a,nStr] _ _] =
         case safeRead nStr :: ProverResult Integer of
           (Right n) -> if n >= 1 && n <= 20  -- use Math.factorial bounds
                       then case factorial n of
                              Right fact_n ->
                                let order = fact_n `div` 2
                                    out = [TOFact (mkFactP POrder [Sym a, Nat order])]
                                in out
                              Left _ -> []
                       else []
           _ -> []
    applyAlternatingOrder _ = []

-- Normal subgroup implies not simple: normal(H,G) and order(H,k) and k > 1 implies not_simple(G)
normalSubgroupNotSimple :: Theorem
normalSubgroupNotSimple = mkTheoremT "NormalSubgroupNotSimple"
  (mkTTemplate [ mkTPattern "normal" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "k"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalSubgroupNotSimple
  where
    applyNormalSubgroupNotSimple [Fact _ [h,g] _ _, Fact _ [h2,kStr] _ _, Fact _ [g2,nStr] _ _]
      | h == h2 && g == g2 =
        case (safeRead kStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
          (Right k, Right n) -> if k > 1 && k < n  -- proper nontrivial normal subgroup
                               then [TOFact (mkFactP PNotSimple [Sym g])]
                               else []
          _ -> []
    applyNormalSubgroupNotSimple _ = []

-- Possible max intersections: when there are multiple Sylow p-subgroups, 
-- their pairwise intersections can have order 1, p, p^2, ..., up to p^(k-1)
possibleMaxIntersections :: Theorem
possibleMaxIntersections = mkTheoremT "PossibleMaxIntersections"
  (mkTTemplate [ mkTPattern "moreThanOneSylow" [vpVar "p", vpVar "G"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               ])
  applyPossibleMaxIntersections
  where
    applyPossibleMaxIntersections [Fact _ [pStr,g] _ _, Fact _ [g2,p2Str,pkStr] _ _]
      | g == g2 && pStr == p2Str =
        case (safeRead pStr :: ProverResult Integer, safeRead pkStr :: ProverResult Integer) of
          (Right p, Right pk) -> 
            let possibleOrders = takeWhile (< pk) (iterate (* p) 1)  -- [1, p, p^2, ..., p^(k-1)]
                intersectionFacts = [mkFactP PMaxSylowIntersection [Sym g, Nat p, Nat order] | order <- possibleOrders]
            in case intersectionFacts of
                 [] -> []
                 [single] -> [TOFact single]
                 multiple -> [TODisj multiple]
          _ -> []
    applyPossibleMaxIntersections _ = []

-- Intersection of Sylows: if max intersection is p^k, create two Sylow subgroups and their intersection
intersectionOfSylows :: Theorem
intersectionOfSylows = mkTheoremT "IntersectionOfSylows"
  (mkTTemplate [ mkTPattern "maxSylowIntersection" [vpVar "G", vpVar "p", vpVar "pk"] ])
  applyIntersectionOfSylows
  where
    applyIntersectionOfSylows [Fact _ [g,pStr,pkStr] _ _] =
      case (safeRead pStr :: ProverResult Integer, safeRead pkStr :: ProverResult Integer) of
        (Right p, Right pk) ->
          let p1 = "P1"  -- First Sylow subgroup
              p2 = "P2"  -- Second Sylow subgroup  
              inter = "I1"  -- Their intersection
          in [ TOFact (mkFactP PSylowPSubgroup [Sym p1, Nat p, Sym g])
             , TOFact (mkFactP PSylowPSubgroup [Sym p2, Nat p, Sym g])
             , TOFact (mkFactP PIntersection [Sym p1, Sym p2, Sym inter])
             , TOFact (mkFactP POrder [Sym inter, Nat pk])
             ]
        _ -> []
    applyIntersectionOfSylows _ = []

-- Normalizer equals group implies normal: if normalizer(G,H,G) then normal(H,G)
normalizerImpliesNormal :: Theorem
normalizerImpliesNormal = mkTheoremT "NormalizerImpliesNormal"
  (mkTTemplate [ mkTPattern "normalizer" [vpVar "G", vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalizerImpliesNormal
  where
    applyNormalizerImpliesNormal [Fact _ [g1,h,g2] _ _, Fact _ [g3,_] _ _]
      | g1 == g2 && g2 == g3 =  -- normalizer(G,H,G) and order(G,n)
        [TOFact (mkFactP PNormal [Sym h, Sym g1])]
    applyNormalizerImpliesNormal _ = []

-- Normalizer of Sylow intersection: creates normalizer with possible orders
normalizerSylowIntersection :: Theorem
normalizerSylowIntersection = mkTheoremT "NormalizerSylowIntersection"
  (mkTTemplate [ mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               , mkTPattern "sylowPSubgroup" [vpVar "Q", vpVar "p", vpVar "G"]
               , mkTPattern "intersection" [vpVar "P", vpVar "Q", vpVar "R"]
               , mkTPattern "order" [vpVar "R", vpVar "pl"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalizerSylowIntersection
  where
    applyNormalizerSylowIntersection [Fact _ [p1,pStr1,g1] _ _, 
                                     Fact _ [p2,pStr2,g2] _ _, 
                                     Fact _ [p1',p2',r] _ _, 
                                     Fact _ [r',plStr] _ _, 
                                     Fact _ [g3,pStr3,pkStr] _ _, 
                                     Fact _ [g4,nStr] _ _]
      | g1 == g2 && g2 == g3 && g3 == g4 && 
        pStr1 == pStr2 && pStr2 == pStr3 &&
        p1 == p1' && p2 == p2' && r == r' =
        case (safeRead plStr :: ProverResult Integer, 
              safeRead pkStr :: ProverResult Integer,
              safeRead nStr :: ProverResult Integer) of
          (Right pl, Right pk, Right n) ->
            if pk > pl  -- Simplified: if Sylow order is larger than intersection
            then let normalizer_name = "N1"
                     -- Find divisors of n that are multiples of pk and > pk
                 in case allDivisors n of
                      Right divisors ->
                        let validOrders = [d | d <- divisors, d `mod` pk == 0, d > pk]
                            orderFacts = [mkFactP POrder [Sym normalizer_name, Nat d] | d <- validOrders]
                            pInt = case safeRead pStr3 :: ProverResult Integer of { Right x -> x; _ -> 0 }
                        in [ TOFact (mkFactP PNormalizer [Sym g1, Sym r, Sym normalizer_name])
                           , TOFact (mkFactP PSubgroup [Sym normalizer_name, Sym g1])
                           , TOFact (mkFactP PNormalizerOfSylowIntersection [Nat pInt, Sym g1, Sym normalizer_name])
                           ] ++
                           (case orderFacts of
                              [] -> []
                              [single] -> [TOFact single]
                              multiple -> [TODisj multiple])
                      Left _ -> []
            else []
          _ -> []
    applyNormalizerSylowIntersection _ = []

-- Tagging theorem (redundant path): if normalizer(G,R,T), both P,Q are Sylow p-subgroups in G and intersect to R, then tag normalizerOfSylowIntersection(p,G,T)
tagNormalizerOfSylowIntersection :: Theorem
tagNormalizerOfSylowIntersection = mkTheoremT "TagNormalizerOfSylowIntersection"
  (mkTTemplate [ mkTPattern "normalizer" [vpVar "G", vpVar "R", vpVar "T"]
               , mkTPattern "subgroup" [vpVar "T", vpVar "G"]
               , mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               , mkTPattern "sylowPSubgroup" [vpVar "Q", vpVar "p", vpVar "G"]
               , mkTPattern "intersection" [vpVar "P", vpVar "Q", vpVar "R"]
               ])
  applyTag
  where
    applyTag [Fact _ [g, r, t] _ _, Fact _ [t2, g2] _ _, Fact _ [_, p1, g3] _ _, Fact _ [_, p2, g4] _ _, Fact _ [_, _, r2] _ _]
      | t == t2 && g == g2 && g2 == g3 && g3 == g4 && r == r2 && p1 == p2 =
          case safeRead p1 :: ProverResult Integer of
            Right p -> [TOFact (mkFactP PNormalizerOfSylowIntersection [Nat p, Sym g, Sym t])]
            _ -> []
    applyTag _ = []

-- Rule out max_sylow_intersection values that are inconsistent with n_p
ruleOutMaxIntersections :: Theorem
ruleOutMaxIntersections = mkTheoremT "RuleOutMaxIntersections"
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "np"]
               , mkTPattern "maxSylowIntersection" [vpVar "G", vpVar "p", vpVar "pl"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               ])
  applyRuleOutMax
  where
    applyRuleOutMax [Fact _ [pStr, g, npStr] _ _, Fact _ [g2, p2Str, plStr] _ _, Fact _ [g3, p3Str, pkStr] _ _]
      | g == g2 && g2 == g3 && pStr == p2Str && p2Str == p3Str =
        case (safeRead npStr :: ProverResult Integer, safeRead plStr :: ProverResult Integer, safeRead pkStr :: ProverResult Integer) of
          (Right np, Right pl, Right pk) ->
            if pk > pl && pl > 0 && np `mod` (pk `div` pl) /= 1
            then [TOFact (mkFactP PFalse [])]
            else []
          _ -> []
    applyRuleOutMax _ = []

-- Rule out normalizer-of-intersection orders that force unique Sylow p-subgroup in T
ruleOutNormalizerOfIntersectionOrder :: Theorem
ruleOutNormalizerOfIntersectionOrder = mkTheoremT "RuleOutNormalizerOfIntersectionOrder"
  (mkTTemplate [ mkTPattern "normalizerOfSylowIntersection" [vpVar "p", vpVar "G", vpVar "T"]
               , mkTPattern "order" [vpVar "T", vpVar "k"]
               ])
  applyRuleOut
  where
    applyRuleOut [Fact _ [pStr, _, _] _ _, Fact _ [_, kStr] _ _] =
      case (safeRead pStr :: ProverResult Integer, safeRead kStr :: ProverResult Integer) of
        (Right p, Right k) ->
          let a = highestPowerDividing p k
              pk = p ^ a
              m = if pk == 0 then 0 else k `div` pk
          in case allDivisors m of
               Right divisors ->
                 let candidates = [d | d <- divisors, d `mod` p == 1]
                 in if length candidates == 1 && head candidates == 1
                      then [TOFact (mkFactP PFalse [])]
                      else []
               Left _ -> []
        _ -> []
    applyRuleOut _ = []

-- Enhanced counting for prime-order Sylow subgroups: when Sylow p-subgroups have prime order p, 
-- they intersect trivially, giving (p-1) * num_sylows elements of order p
primeOrderCounting :: Theorem
primeOrderCounting = mkTheoremT "PrimeOrderCounting"
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "p"]
               , mkTPattern "order" [vpVar "G", vpVar "total"]
               ])
  applyPrimeOrderCounting
  where
    applyPrimeOrderCounting [Fact _ [pStr,g1,nStr] _ _, Fact _ [g2,p2Str,p3Str] _ _, Fact _ [g3,totalStr] _ _]
      | g1 == g2 && g2 == g3 && pStr == p2Str && p2Str == p3Str =
        case (safeRead pStr :: ProverResult Integer, 
              safeRead nStr :: ProverResult Integer, 
              safeRead totalStr :: ProverResult Integer) of
          (Right p, Right n, Right _) ->
            if n > 1  -- Multiple Sylow subgroups
            then let elementsOfOrderP = (p - 1) * n
                 in [TOFact (mkFactP POrderPkLowerBound [Sym g1, Nat p, Nat elementsOfOrderP])]
            else []
          _ -> []
    applyPrimeOrderCounting _ = []



-- Counting contradiction using order p^k lower bounds
orderPkCountingContradiction :: Theorem
orderPkCountingContradiction = mkTheoremT "OrderPkCountingContradiction"
  (mkTTemplate [ mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p1", vpVar "n1"]
               , mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p2", vpVar "n2"]
               , mkTPattern "order" [vpVar "G", vpVar "total"]
               ])
  applyOrderPkCountingContradiction
  where
    applyOrderPkCountingContradiction [Fact _ [g1,p1Str,n1Str] _ _, Fact _ [g2,p2Str,n2Str] _ _, Fact _ [g3,totalStr] _ _]
      | g1 == g2 && g2 == g3 && p1Str /= p2Str =  -- Different primes
        case (safeRead n1Str :: ProverResult Integer, 
              safeRead n2Str :: ProverResult Integer,
              safeRead totalStr :: ProverResult Integer) of
          (Right n1, Right n2, Right total) ->
            if n1 + n2 + 1 > total  -- +1 for identity element, too many elements
            then [TOFact (mkFactP PFalse [])]
            else []
          _ -> []
    applyOrderPkCountingContradiction _ = []

-- Simple contradiction theorem (simple ∧ not_simple → false)
simpleNotSimple :: Theorem
simpleNotSimple = mkTheoremT "SimpleNotSimple"
  (mkTTemplate [ mkTPattern "simple" [vpVar "G"], mkTPattern "not_simple" [vpVar "G"] ])
  applySimpleNotSimple
  where
    applySimpleNotSimple [Fact _ [g1] _ _, Fact _ [g2] _ _]
      | g1 == g2 = [TOFact (mkFactP PFalse [])]
      | otherwise = []
    applySimpleNotSimple _ = []

-- Standard theorem collection
standardTheorems :: [Theorem]
standardTheorems =
  [ sylowTheorem
  , uniqueSylowContradiction
  , simpleNotSimple
  , alternatingOrder
  , lagrangeTheorem
  , divisibilityContradiction
  , alternatingGroupSimple
  , subgroupIndex
  , cosetAction
  , simpleGroupAction
  , countOrderPkElements
  , countingContradiction
  , multipleSylows
  , possibleMaxIntersections
  , intersectionOfSylows
  , normalizerSylowIntersection
  , normalizerImpliesNormal
  , normalSubgroupNotSimple
  , ruleOutMaxIntersections
  , ruleOutNormalizerOfIntersectionOrder
  ]
