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
sylowTheorem = mkTheoremT "SylowDivisibilityCongruence" 5
  (mkTTemplate [ mkTPattern "group" [vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySylow
  where
    applySylow [_, Fact _ [_, Nat n] _ _] =
      case primeFactorization n of
        Right factors -> 
          let makeConstraint (p, k) = 
                let pk = p ^ k
                    m = n `div` pk
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
                  Left _ -> [TOFact (mkFactP PFalse [])]
          in concat $ map makeConstraint factors
        Left _ -> [TOFact (mkFactP PFalse [])]
    applySylow _ = []

-- If there's a unique Sylow p-subgroup in a simple group, contradiction
-- (only applies when the Sylow subgroup is proper)
uniqueSylowContradiction :: Theorem
uniqueSylowContradiction = mkTheoremT "UniqueSylowImpliesNotSimple" 2
  (mkTTemplate [ mkTPattern "simple" [vpVar "G"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpFixed (Nat 1)]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyUniqueSylow
  where
    applyUniqueSylow [_, _, Fact _ [_, _, pkVal] _ _, Fact _ [_, nVal] _ _] =
      case (pkVal, nVal) of
        (Nat pk, Nat n) -> if pk > 1 && pk < n then [TOFact (mkFactP PFalse [])] else []
        _ -> []
    applyUniqueSylow _ = []

-- Generate Sylow p-subgroup facts when needed for counting
sylowPSubgroupGeneration :: Theorem
sylowPSubgroupGeneration = mkTheoremT "SylowPSubgroupGeneration" 20
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               ])
  applySylowPGeneration
  where
    applySylowPGeneration [Fact _ [Nat p, Sym g, _] _ _, Fact _ [Sym g2, Nat p2, Nat pk] _ _]
      | g == g2 && p == p2 =
        let sylowName = "S" ++ g
        in [ TOFact (mkFactP PSylowPSubgroup [Sym sylowName, Nat p, Sym g])
           , TOFact (mkFactP POrder [Sym sylowName, Nat pk])
           ]
    applySylowPGeneration _ = []



-- Action on Sylow subgroups: if n_p > 1, G acts on them.

-- Embedding in alternating group: if G is simple and has n_p > 1 Sylow p-subgroups, then G embeds in A_{n_p}
embedInAlternating :: Theorem
embedInAlternating = mkTheoremT "EmbedInAlternating" 15
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "simple" [vpVar "G"]
               ])
  applyEmbedInAlternating
  where
    applyEmbedInAlternating [Fact _ [_, Sym g, Nat np] _ _, Fact _ [Sym g2] _ _]
      | g == g2 && np > 1 =
          let altName = "A" ++ show np
          in [TOFact (mkFactP PSubgroup [Sym g, Sym altName]), TOFact (mkFactP PAlternatingGroup [Sym altName, Nat np])]
    applyEmbedInAlternating _ = []

-- Any transitive action of degree n yields a faithful embedding G ↪ S_n (encode as embedsInSym)
actionEmbedsInSym :: Theorem
actionEmbedsInSym = mkTheoremT "ActionEmbedsInSym" 20
  (mkTTemplate [ mkTPattern "transitiveAction" [vpVar "G", vpVar "n"] ])
  applyActionEmbeds
  where
    applyActionEmbeds [Fact _ [Sym g, Nat n] _ _] =
      [TOFact (mkFactP PEmbedsInSym [Sym g, SymGroup n])]
    applyActionEmbeds _ = []

-- Order must divide symmetric group order
orderDividesSym :: Theorem
orderDividesSym = mkTheoremT "OrderMustDivideSym" 5
  (mkTTemplate [ mkTPattern "embedsInSym" [vpVar "G", vpVar "Sn"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySymDivision
  where
    applySymDivision [Fact _ [_, snVal] _ _, Fact _ [_, nVal] _ _] =
      case (nVal, snVal) of
        (Nat n, SymGroup sn) -> case factorial sn of
          Right factM -> 
            if factM `mod` n /= 0 
               then [TOFact (mkFactP PFalse [])]
               else []
          Left _ -> [TOFact (mkFactP PFalse [])] -- Factorial error
        _ -> [TOFact (mkFactP PFalse [])] -- Parse error
    applySymDivision _ = []

orderDividesAlt :: Theorem
orderDividesAlt = mkTheoremT "OrderMustDivideAlt" 5
  (mkTTemplate [ mkTPattern "embedInAlt" [vpVar "G", vpVar "An"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyDivision
  where
    applyDivision [Fact _ [_, aVal] _ _, Fact _ [_, nVal] _ _] =
      case (aVal, nVal) of
        (AltGroup m, Nat n) -> case factorial m of
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
countOrderPkElements = mkTheoremT "CountOrderPkElements" 20
  (mkTTemplate [ mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "order" [vpVar "P", vpVar "pk"]
               ])
  applyCountOrderPkElements
  where
    applyCountOrderPkElements [Fact _ [pVal, pStr1Val, gVal] _ _, Fact _ [pStr2Val, g2Val, npVal] _ _, Fact _ [p2Val, pkVal] _ _]
      | pStr1Val == pStr2Val && gVal == g2Val && pVal == p2Val =
          case (pStr1Val, npVal, pkVal, gVal) of
            (Nat prime, Nat numSylow, Nat pk, Sym g) ->
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
countingContradiction = mkTheoremT "CountingContradiction" 2
  (mkTTemplate [ mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p1", vpVar "N1"]
               , mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p2", vpVar "N2"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyCountingContradiction
  where
    applyCountingContradiction [Fact _ [_,p1Val,n1Val] _ _, 
                               Fact _ [_,p2Val,n2Val] _ _, 
                               Fact _ [_,nVal] _ _] =
      case (p1Val, p2Val, n1Val, n2Val, nVal) of
        (Nat p1, Nat p2, Nat n1, Nat n2, Nat n) ->
          if p1 /= p2 && n1 + n2 + 1 > n  -- +1 for identity element
          then [TOFact (mkFactP PFalse [])]
          else []
        _ -> []
    applyCountingContradiction _ = []

-- Lagrange's theorem: order of subgroup divides order of group
lagrangeTheorem :: Theorem
lagrangeTheorem = mkTheoremT "LagrangeTheorem" 2
  (mkTTemplate [ mkTPattern "subgroup" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyLagrange
  where
    applyLagrange [Fact _ [hVal, gVal] _ _, Fact _ [h2Val, mVal] _ _, Fact _ [g2Val, nVal] _ _]
      | hVal == h2Val && gVal == g2Val =
        case (mVal, nVal) of
          (Nat m, Nat n) -> [TOFact (mkFactP PDivides [Nat m, Nat n])]
          _ -> []
    applyLagrange _ = []

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't

-- Divisibility contradiction: if m should divide n but doesn't
divisibilityContradiction :: Theorem
divisibilityContradiction = mkTheoremT "DivisibilityContradiction" 1
  (mkTTemplate [ mkTPattern "divides" [vpVar "m", vpVar "n"] ])
  applyDivisibilityContradiction
  where
    applyDivisibilityContradiction [Fact _ [mVal,nVal] _ _] =
         case (mVal, nVal) of
           (Nat m, Nat n) -> 
             if n `mod` m /= 0
             then [TOFact (mkFactP PFalse [])]
             else []
           _ -> []
    applyDivisibilityContradiction _ = []

-- A_n is simple for n >= 5
alternatingGroupSimple :: Theorem
alternatingGroupSimple = mkTheoremT "AlternatingGroupSimple" 5
  (mkTTemplate [ mkTPattern "alternatingGroup" [vpVar "A", vpVar "n"] ])
  applyAlternatingSimple
  where
    applyAlternatingSimple [Fact _ [aVal,nVal] _ _] =
      case nVal of
        Nat n -> if n >= 5
                  then case aVal of Sym a -> [TOFact (mkFactP PSimple [Sym a])]; _ -> []
                  else []
        _ -> []
    applyAlternatingSimple _ = []

-- Subgroup index theorem: |G:H| = |G| / |H|
subgroupIndex :: Theorem
subgroupIndex = mkTheoremT "SubgroupIndex" 5
  (mkTTemplate [ mkTPattern "subgroup" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               ])
  applySubgroupIndex
  where
    applySubgroupIndex [Fact _ [hVal,gVal] _ _, Fact _ [g2Val,nVal] _ _, Fact _ [h2Val,mVal] _ _]
      | gVal == g2Val && hVal == h2Val =
        case (hVal, gVal, nVal, mVal) of
          (Sym h, Sym g, Nat n, Nat m) -> 
            if m > 0 && n `mod` m == 0
            then [TOFact (mkFactP PIndex [Sym h, Sym g, Nat (n `div` m)])]
            else []
          _ -> []
    applySubgroupIndex _ = []

-- Coset action theorem: G acts transitively on cosets of H with index n
cosetAction :: Theorem
cosetAction = mkTheoremT "CosetAction" 5
  (mkTTemplate [ mkTPattern "index" [vpVar "H", vpVar "G", vpVar "n"] ])
  applyCosetAction
  where
    applyCosetAction [Fact _ [_,gVal,nVal] _ _] =
      case (gVal, nVal) of
        (Sym g, Nat n) -> [TOFact (mkFactP PTransitiveAction [Sym g, Nat n])]
        _ -> []
    applyCosetAction _ = []

-- Simple group action theorem: if G is simple and has n_p > 1 Sylow p-subgroups, it embeds in A_{n_p}
simpleGroupAction :: Theorem
simpleGroupAction = mkTheoremT "EmbedsIntoSnBySylowAction" 20
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "simple" [vpVar "G"]
               ])
  applySimpleGroupAction
  where
    applySimpleGroupAction [Fact _ [_,gVal,npVal] _ _, Fact _ [g2Val] _ _]
      | gVal == g2Val =
        case (gVal, npVal) of
          (Sym g, Nat n) -> if n > 1 && n <= 20
              then [TOFact (mkFactP PEmbedsInSym [Sym g, SymGroup n])]
              else []
          _ -> []
    applySimpleGroupAction _ = []

-- Multiple Sylows theorem: if num_sylow(p,G,n) where n > 1, then more_than_one_sylow(p,G)
multipleSylows :: Theorem
multipleSylows = mkTheoremT "MultipleSylows" 2
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"] ])
  applyMultipleSylows
  where
    applyMultipleSylows [Fact _ [pVal,gVal,nVal] _ _] =
      case (pVal, gVal, nVal) of
        (Nat pInt, Sym g, Nat n) -> if n > 1
                      then [TOFact (mkFactP PMoreThanOneSylow [Nat pInt, Sym g])]
                      else []
        _ -> []
    applyMultipleSylows _ = []

-- Alternating order theorem: alternating_group(A,n) implies order(A, n!/2)
alternatingOrder :: Theorem
alternatingOrder = mkTheoremT "AlternatingOrder" 10
  (mkTTemplate [ mkTPattern "alternatingGroup" [vpVar "A", vpVar "n"] ])
  applyAlternatingOrder
  where
    applyAlternatingOrder [Fact _ [aVal,nVal] _ _] =
         case (aVal, nVal) of
           (Sym a, Nat n) -> if n >= 1 && n <= 20  -- use Math.factorial bounds
                       then case factorial n of
                              Right fact_n ->
                                let order = fact_n `div` 2
                                    out = [TOFact (mkFactP POrder [Sym a, Nat order])]
                                in out
                              Left _ -> []
                       else []
           _ -> []
    applyAlternatingOrder _ = []

-- Lagrange for alternating groups: if subgroup(H,G) and order(H,m) and order(G,n), then divides(m,n)
lagrangeAlternating :: Theorem
lagrangeAlternating = mkTheoremT "LagrangeAlternating" 5
  (mkTTemplate [ mkTPattern "subgroup" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyLagrangeAlternating
  where
    applyLagrangeAlternating [Fact _ [hVal,gVal] _ _, Fact _ [h2Val,mVal] _ _, Fact _ [g2Val,nVal] _ _]
      | hVal == h2Val && gVal == g2Val =
        case (mVal, nVal) of
          (Nat m, Nat n) -> [TOFact (mkFactP PDivides [Nat m, Nat n])]
          _ -> []
    applyLagrangeAlternating _ = []

-- Normal subgroup implies not simple: normal(H,G) and order(H,k) and k > 1 implies not_simple(G)
normalSubgroupNotSimple :: Theorem
normalSubgroupNotSimple = mkTheoremT "NormalSubgroupNotSimple" 2
  (mkTTemplate [ mkTPattern "normal" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "k"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalSubgroupNotSimple
  where
    applyNormalSubgroupNotSimple [Fact _ [hVal,gVal] _ _, Fact _ [h2Val,kVal] _ _, Fact _ [g2Val,nVal] _ _]
      | hVal == h2Val && gVal == g2Val =
        case (gVal, kVal, nVal) of
          (Sym g, Nat k, Nat n) -> if k > 1 && k < n
                               then [TOFact (mkFactP PNotSimple [Sym g])]
                               else []
          _ -> []
    applyNormalSubgroupNotSimple _ = []

-- Possible max intersections: when there are multiple Sylow p-subgroups, 
-- their pairwise intersections can have order 1, p, p^2, ..., up to p^(k-1)
possibleMaxIntersections :: Theorem
possibleMaxIntersections = mkTheoremT "PossibleMaxIntersections" 25
  (mkTTemplate [ mkTPattern "moreThanOneSylow" [vpVar "p", vpVar "G"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               ])
  applyPossibleMaxIntersections
  where
    applyPossibleMaxIntersections [Fact _ [pVal,gVal] _ _, Fact _ [g2Val,p2Val,pkVal] _ _]
      | gVal == g2Val && pVal == p2Val =
        case (gVal, pVal, pkVal) of
          (Sym g, Nat p, Nat pk) -> 
            let possibleOrders = takeWhile (< pk) (iterate (* p) 1)
                intersectionFacts = [mkFactP PMaxSylowIntersection [Sym g, Nat p, Nat order] | order <- possibleOrders]
            in case intersectionFacts of
                 [] -> []
                 [single] -> [TOFact single]
                 multiple -> [TODisj multiple]
          _ -> []
    applyPossibleMaxIntersections _ = []

-- Intersection of Sylows: if max intersection is p^k, create two Sylow subgroups and their intersection
intersectionOfSylows :: Theorem
intersectionOfSylows = mkTheoremT "IntersectionOfSylows" 30
  (mkTTemplate [ mkTPattern "maxSylowIntersection" [vpVar "G", vpVar "p", vpVar "pk"] ])
  applyIntersectionOfSylows
  where
    applyIntersectionOfSylows [Fact _ [gVal,pVal,pkVal] _ _] =
      case (gVal, pVal, pkVal) of
        (Sym g, Nat p, Nat pk) ->
          let p1 = "P1"
              p2 = "P2"
              inter = "I1"
          in [ TOFact (mkFactP PSylowPSubgroup [Sym p1, Nat p, Sym g])
             , TOFact (mkFactP PSylowPSubgroup [Sym p2, Nat p, Sym g])
             , TOFact (mkFactP PIntersection [Sym p1, Sym p2, Sym inter])
             , TOFact (mkFactP POrder [Sym inter, Nat pk])
             ]
        _ -> []
    applyIntersectionOfSylows _ = []

-- Normalizer equals group implies normal: if normalizer(G,H,G) then normal(H,G)
normalizerImpliesNormal :: Theorem
normalizerImpliesNormal = mkTheoremT "NormalizerImpliesNormal" 5
  (mkTTemplate [ mkTPattern "normalizer" [vpVar "G", vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalizerImpliesNormal
  where
    applyNormalizerImpliesNormal [Fact _ [g1Val,hVal,g2Val] _ _, Fact _ [g3Val,_] _ _]
      | g1Val == g2Val && g2Val == g3Val =
        case (hVal, g1Val) of
          (Sym h, Sym g1) -> [TOFact (mkFactP PNormal [Sym h, Sym g1])]
          _ -> []
    applyNormalizerImpliesNormal _ = []

-- Normalizer of Sylow intersection: creates normalizer with possible orders
normalizerSylowIntersection :: Theorem
normalizerSylowIntersection = mkTheoremT "NormalizerSylowIntersection" 40
  (mkTTemplate [ mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               , mkTPattern "sylowPSubgroup" [vpVar "Q", vpVar "p", vpVar "G"]
               , mkTPattern "intersection" [vpVar "P", vpVar "Q", vpVar "R"]
               , mkTPattern "order" [vpVar "R", vpVar "pl"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalizerSylowIntersection
  where
    applyNormalizerSylowIntersection [Fact _ [p1Val,pStr1Val,g1Val] _ _, 
                                     Fact _ [p2Val,pStr2Val,g2Val] _ _, 
                                     Fact _ [p1'Val,p2'Val,rVal] _ _, 
                                     Fact _ [r'Val,plVal] _ _, 
                                     Fact _ [g3Val,pStr3Val,pkVal] _ _, 
                                     Fact _ [g4Val,nVal] _ _]
      | g1Val == g2Val && g2Val == g3Val && g3Val == g4Val && 
        pStr1Val == pStr2Val && pStr2Val == pStr3Val &&
        p1Val == p1'Val && p2Val == p2'Val && rVal == r'Val =
        case (g1Val, rVal, plVal, pkVal, nVal) of
          (Sym g1, Sym r, Nat pl, Nat pk, Nat n) ->
            if pk > pl
            then 
              let normalizer_name = "N1"
                  validOrders = [d | d <- [1..n], d `mod` pk == 0, d > pk]
                  orderFacts = [mkFactP POrder [Sym normalizer_name, Nat d] | d <- validOrders]
                  mainFacts = [ TOFact (mkFactP PNormalizer [Sym g1, Sym r, Sym normalizer_name])
                              , TOFact (mkFactP PSubgroup [Sym normalizer_name, Sym g1])
                              ]
                  extraFacts = case orderFacts of
                                 [] -> []
                                 [single] -> [TOFact single]
                                 multiple -> [TODisj multiple]
              in mainFacts ++ extraFacts
            else []
          _ -> []
    applyNormalizerSylowIntersection _ = []

-- Rule out impossible normalizer orders: if normalizer forces unique Sylow subgroup, contradiction
normalizerOrderContradiction :: Theorem
normalizerOrderContradiction = mkTheoremT "NormalizerOrderContradiction" 15
  (mkTTemplate [ mkTPattern "normalizer" [vpVar "G", vpVar "H", vpVar "N"]
               , mkTPattern "order" [vpVar "N", vpVar "k"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyNormalizerOrderContradiction
  where
    applyNormalizerOrderContradiction [Fact _ [g1Val,_,n1Val] _ _, Fact _ [n2Val,kVal] _ _, Fact _ [g2Val,nVal] _ _]
      | g1Val == g2Val && n1Val == n2Val =
        case (g1Val, kVal, nVal) of
          (Sym g1, Nat k, Nat n) ->
            let index = n `div` k
            in if index > 1 && index <= 4
               then [ TOFact (mkFactP PSubgroup [Sym g1, Sym "A"])
                    , TOFact (mkFactP PAlternatingGroup [Sym "A", Nat index])
                    , TOFact (mkFactP PDivides [Nat n,
                          case factorial index of
                            Right fact_n -> Nat (fact_n `div` 2)
                            Left _ -> Nat 1])
                    ]
               else []
          _ -> []
    applyNormalizerOrderContradiction _ = []

-- Legacy conversion theorems were removed; the prover uses typed encodings exclusively.

-- Enhanced counting for prime-order Sylow subgroups: when Sylow p-subgroups have prime order p, 
-- they intersect trivially, giving (p-1) * num_sylows elements of order p
primeOrderCounting :: Theorem
primeOrderCounting = mkTheoremT "PrimeOrderCounting" 10
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "p"]
               , mkTPattern "order" [vpVar "G", vpVar "total"]
               ])
  applyPrimeOrderCounting
  where
    applyPrimeOrderCounting [Fact _ [pVal,g1Val,nVal] _ _, Fact _ [g2Val,p2Val,p3Val] _ _, Fact _ [g3Val,totalVal] _ _]
      | g1Val == g2Val && g2Val == g3Val && pVal == p2Val && p2Val == p3Val =
        case (g1Val, pVal, nVal) of
          (Sym g1, Nat p, Nat n) ->
            if n > 1
            then let elementsOfOrderP = (p - 1) * n
                 in [TOFact (mkFactP POrderPkLowerBound [Sym g1, Nat p, Nat elementsOfOrderP])]
            else []
          _ -> []
    applyPrimeOrderCounting _ = []



-- Counting contradiction using order p^k lower bounds
orderPkCountingContradiction :: Theorem
orderPkCountingContradiction = mkTheoremT "OrderPkCountingContradiction" 2
  (mkTTemplate [ mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p1", vpVar "n1"]
               , mkTPattern "orderPkLowerBound" [vpVar "G", vpVar "p2", vpVar "n2"]
               , mkTPattern "order" [vpVar "G", vpVar "total"]
               ])
  applyOrderPkCountingContradiction
  where
    applyOrderPkCountingContradiction [Fact _ [g1Val,p1Val,n1Val] _ _, Fact _ [g2Val,p2Val,n2Val] _ _, Fact _ [g3Val,totalVal] _ _]
      | g1Val == g2Val && g2Val == g3Val && p1Val /= p2Val =
        case (n1Val, n2Val, totalVal) of
          (Nat n1, Nat n2, Nat total) ->
            if n1 + n2 + 1 > total
            then [TOFact (mkFactP PFalse [])]
            else []
          _ -> []
    applyOrderPkCountingContradiction _ = []

-- Simple contradiction theorem (simple ∧ not_simple → false)
simpleNotSimple :: Theorem
simpleNotSimple = mkTheoremT "SimpleNotSimple" 2
  (mkTTemplate [ mkTPattern "simple" [vpVar "G"], mkTPattern "not_simple" [vpVar "G"] ])
  applySimpleNotSimple
  where
    applySimpleNotSimple [Fact _ [g1] _ _, Fact _ [g2] _ _]
      | g1 == g2 = [TOFact (mkFactP PFalse [])]
      | otherwise = []
    applySimpleNotSimple _ = []

-- A group cannot have two different orders
-- uniqueOrderTheorem :: Theorem
-- uniqueOrderTheorem = mkTheoremT "UniqueOrder" 1
--   (mkTTemplate [ mkTPattern "order" [vpVar "G", vpVar "n1"]
--                , mkTPattern "order" [vpVar "G", vpVar "n2"]
--                ])
--   applyUniqueOrder
--   where
--     applyUniqueOrder [Fact _ [_, n1Val] _ _, Fact _ [_, n2Val] _ _] =
--       if n1Val /= n2Val then [TOFact (mkFactP PFalse [])] else []
--     applyUniqueOrder _ = []

-- Standard theorem collection
standardTheorems :: [Theorem]
standardTheorems = 
  [ sylowTheorem
  , uniqueSylowContradiction
  , sylowPSubgroupGeneration
  , embedInAlternating
  -- legacy conversions removed
  , orderDividesSym
  , orderDividesAlt
  , sylowNormalizerIndex
  -- , normalizerAutBoundPrime  -- DISABLED: This theorem is too restrictive and causes false contradictions
  , countOrderPkElements
  , countingContradiction
  , lagrangeTheorem
  , lagrangeAlternating
  , divisibilityContradiction
  , alternatingGroupSimple
  , subgroupIndex
  , cosetAction
  -- , simpleGroupAction  -- DISABLED: This theorem is incorrect and causes false contradictions
  , multipleSylows
  , alternatingOrder
  , normalSubgroupNotSimple
  , possibleMaxIntersections
  , intersectionOfSylows
  , normalizerImpliesNormal
  , normalizerSylowIntersection
  , normalizerOrderContradiction
  , primeOrderCounting
  , orderPkCountingContradiction
  , simpleNotSimple
  ]

-- New: If there are n_p Sylow p-subgroups of G, then index(N_G(P)) = n_p
-- We record index(N,P) = n_p as a fact, and if order(G,n) and order(P,p) with p prime, we can derive order of normalizer divides n with index n_p
sylowNormalizerIndex :: Theorem
sylowNormalizerIndex = mkTheoremT "SylowNormalizerIndex" 15
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               ])
  applySylowNormalizerIndex
  where
    applySylowNormalizerIndex [Fact _ [pVal,gVal,npVal] _ _, Fact _ [p2Val,p3Val,g2Val] _ _]
      | gVal == g2Val && pVal == p2Val && p2Val == p3Val =
          case (gVal, npVal) of
            (Sym g, Nat np) ->
              [ TOFact (mkFactP PIndex [Sym "N", Sym "G", Nat np])
              , TOFact (mkFactP PSubgroup [Sym "N", Sym "G"])
              , TOFact (mkFactP PNormalizer [Sym g, Sym "P", Sym "N"])
              ]
            _ -> []
    applySylowNormalizerIndex _ = []

-- New: If P is a Sylow p-subgroup of prime order p and n_p > 1, then n_p | (p-1)
-- Encoded as: when sylowOrder(G,p,p) and numSylow(p,G,n) with n>1, then divides(n, p-1)
normalizerAutBoundPrime :: Theorem
normalizerAutBoundPrime = mkTheoremT "NormalizerAutBoundPrime" 15
  (mkTTemplate [ mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "p"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "G", vpVar "N"]
               ])
  applyAutBound
  where
    applyAutBound [Fact _ [g1Val,p1Val,_] _ _, Fact _ [p2Val,g2Val,nVal] _ _, Fact _ [g3Val,_] _ _]
      | g1Val == g2Val && g2Val == g3Val && p1Val == p2Val =
          case (nVal, p1Val) of
            (Nat n, Nat p) -> if n > 1
                                  then [TOFact (mkFactP PDivides [Nat n, Nat (p-1)])]
                                  else []
            _ -> []
    applyAutBound _ = []