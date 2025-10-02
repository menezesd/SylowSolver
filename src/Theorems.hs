-- | Standard theorems for the Sylow solver
module Theorems where

import Types
import Math
import Errors
import Data.List (isPrefixOf)
import Data.Maybe (mapMaybe)
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Debug.Trace (trace)

-- Helper for creating facts
fact :: String -> [String] -> Fact
fact name args = Fact name args mempty Nothing

-- Sylow's theorem - generates constraints on number of Sylow p-subgroups
sylowTheorem :: Theorem
sylowTheorem = Theorem "SylowDivisibilityCongruence" 
  (Template [fact "group" ["G"], fact "order" ["G","n"]])
  applySylow
  where
    applySylow [_, Fact _ [_, nStr] _ _] =
      case safeRead nStr of
        Right n -> case primeFactorization n of
          Right factors -> 
            let makeConstraint (p, k) = 
                  let pk = p ^ k
                      m = n `div` pk  -- n = p^k * m, so m = n / p^k
                      -- Generate sylow_order fact
                      orderFact = TOFact (fact "sylowOrder" ["G", show p, show pk])
                  in case allDivisors m of
                    Right divisors ->
                      let validCounts = [d | d <- divisors, d `mod` p == 1]
                          alternatives = [fact "numSylow" [show p, "G", show d] | d <- validCounts]
                          countConstraint = case alternatives of
                                              [] -> TOFact (fact "false" [])
                                              [single] -> TOFact single  
                                              multiple -> TODisj multiple
                      in [orderFact, countConstraint]
                    Left _ -> [TOFact (fact "false" [])] -- Error case
            in concat $ map makeConstraint factors
          Left _ -> [TOFact (fact "false" [])] -- Error case
        Left _ -> [TOFact (fact "false" [])] -- Parse error case
    applySylow _ = []

-- If there's a unique Sylow p-subgroup in a simple group, contradiction
-- (only applies when the Sylow subgroup is proper)
uniqueSylowContradiction :: Theorem
uniqueSylowContradiction = Theorem "UniqueSylowImpliesNotSimple" 
  (Template [fact "simple" ["G"], fact "numSylow" ["p","G","*1"], fact "sylowOrder" ["G","p","pk"], fact "order" ["G","n"]])
  applyUniqueSylow
  where
    applyUniqueSylow [_, Fact _ [pStr, _, _] _ _, Fact _ [_, p2Str, pkStr] _ _, Fact _ [_, nStr] _ _]
      | pStr == p2Str =
        case (safeRead pkStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
          (Right pk, Right n) -> 
            -- Only apply if p^k < n (proper subgroup)
            if pk < n then [TOFact (fact "false" [])] else []
          _ -> []
    applyUniqueSylow _ = []

-- Generate Sylow p-subgroup facts when needed for counting
sylowPSubgroupGeneration :: Theorem
sylowPSubgroupGeneration = Theorem "SylowPSubgroupGeneration"
  (Template [fact "numSylow" ["p","G","n"], fact "sylowOrder" ["G","p","pk"]])
  applySylowPGeneration
  where
    applySylowPGeneration [Fact _ [pStr,g,nStr] _ _, Fact _ [g2,p2Str,pkStr] _ _]
      | g == g2 && pStr == p2Str =
        let sylowName = "S" ++ pStr  -- Generate Sylow p-subgroup name
        in [TOFact (fact "sylowPSubgroup" [sylowName, pStr, g]),
            TOFact (fact "order" [sylowName, pkStr])]
    applySylowPGeneration _ = []



-- Action on Sylow subgroups: if n_p > 1, G acts on them.
actionOnSylowSubgroups :: Theorem
actionOnSylowSubgroups = Theorem "ActionOnSylowSubgroups"
  (Template [fact "numSylow" ["p","G","n_p"]])
  applyAction
  where
    applyAction [Fact _ [_,g,npStr] _ _] =
      case safeRead npStr of
        Right np -> if np > 1 
                    then [TOFact (fact "transitiveAction" [g, npStr])]
                    else []
        _ -> []
    applyAction _ = []

-- Any transitive action of degree n yields a faithful embedding G ↪ S_n (encode as embedsInSym)
actionEmbedsInSym :: Theorem
actionEmbedsInSym = Theorem "ActionEmbedsInSym"
  (Template [fact "transitiveAction" ["G","n"]])
  applyActionEmbeds
  where
    applyActionEmbeds [Fact _ [g, nStr] _ _] =
      -- Represent S_n as the string "S" ++ n
      [TOFact (fact "embedsInSym" [g, "S" ++ nStr])]
    applyActionEmbeds _ = []

-- Order must divide symmetric group order
orderDividesSym :: Theorem
orderDividesSym = Theorem "OrderMustDivideSym"
  (Template [fact "embedsInSym" ["G","Sn"], fact "order" ["G","n"]])
  applySymDivision
  where
    applySymDivision [Fact _ [_, snStr] _ _, Fact _ [_, nStr] _ _] =
      case (safeRead nStr, extractN snStr) of
        (Right groupOrder, Right m) -> case factorial m of
          Right factM -> 
            if factM `mod` groupOrder /= 0 
               then [TOFact (fact "false" [])]
               else []
          Left _ -> [TOFact (fact "false" [])] -- Factorial error
        _ -> [TOFact (fact "false" [])] -- Parse error
      where
        extractN sn = if take 1 sn == "S"
                     then safeRead (drop 1 sn) :: ProverResult Integer
                     else Left $ ParseError "Not a symmetric group"
    applySymDivision _ = []

-- Order must divide alternating group order
orderDividesAlt :: Theorem
orderDividesAlt = Theorem "OrderMustDivideAlt"
  (Template [fact "embedInAlt" ["G","m"], fact "order" ["G","n"]])
  applyDivision
  where
    applyDivision [Fact _ [_, mStr] _ _, Fact _ [_, nStr] _ _] =
      case (safeRead mStr, safeRead nStr) of
        (Right m, Right n) -> case factorial m of
          Right factM -> 
            let altOrder = factM `div` 2
            in if altOrder `mod` n /= 0 
               then [TOFact (fact "false" [])]
               else []
          Left _ -> [TOFact (fact "false" [])] -- Factorial error
        _ -> [TOFact (fact "false" [])] -- Parse error
    applyDivision _ = []

-- Count elements of order p^k in Sylow p-subgroups (match Python pattern)
countOrderPkElements :: Theorem
countOrderPkElements = Theorem "CountOrderPkElements"
  (Template [fact "sylowPSubgroup" ["P","p","G"], fact "numSylow" ["p","G","n_p"], fact "order" ["P","pk"]])
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
              in [TOFact (fact "orderPkLowerBound" [g, pStr1, show lowerBound])]
            _ -> []
    applyCountOrderPkElements _ = []
    applyCount _ = []

-- Counting contradiction: if sum of elements exceeds group order
countingContradiction :: Theorem  
countingContradiction = Theorem "CountingContradiction"
  (Template [fact "orderPkLowerBound" ["G","p1","N1"], 
             fact "orderPkLowerBound" ["G","p2","N2"], 
             fact "order" ["G","n"]])
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
          then [TOFact (fact "false" [])]
          else []
        _ -> []
    applyCountingContradiction _ = []

-- Lagrange's theorem: order of subgroup divides order of group
lagrangeTheorem :: Theorem
lagrangeTheorem = Theorem "LagrangeTheorem"
  (Template [fact "subgroup" ["H","G"], fact "order" ["H","m"], fact "order" ["G","n"]])
  applyLagrange
  where
    applyLagrange [Fact _ [h,g] deps1 _, Fact _ [h2,mStr] deps2 _, Fact _ [g2,nStr] deps3 _]
      | h == h2 && g == g2 =
           case (safeRead mStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
             (Right m, Right n) ->
               [TOFact (fact "divides" [mStr, nStr])]
             _ -> []
    applyLagrange _ = []

-- Divisibility contradiction: if m should divide n but doesn't
divisibilityContradiction :: Theorem
divisibilityContradiction = Theorem "DivisibilityContradiction"
  (Template [fact "divides" ["m","n"]])
  applyDivisibilityContradiction
  where
    applyDivisibilityContradiction [Fact _ [mStr,nStr] deps _] =
         case (safeRead mStr, safeRead nStr) of
           (Right m, Right n) -> 
             if n `mod` m /= 0
             then [TOFact (fact "false" [])]
             else []
           _ -> []
    applyDivisibilityContradiction _ = []

-- A_n is simple for n >= 5
alternatingGroupSimple :: Theorem
alternatingGroupSimple = Theorem "AlternatingGroupSimple"
  (Template [fact "alternatingGroup" ["A","n"]])
  applyAlternatingSimple
  where
    applyAlternatingSimple [Fact _ [a,nStr] _ _] =
      case safeRead nStr of
        Right n -> if n >= 5
                  then [TOFact (fact "simple" [a])]
                  else []
        _ -> []
    applyAlternatingSimple _ = []

-- Subgroup index theorem: |G:H| = |G| / |H|
subgroupIndex :: Theorem
subgroupIndex = Theorem "SubgroupIndex"
  (Template [fact "subgroup" ["H","G"], fact "order" ["G","n"], fact "order" ["H","m"]])
  applySubgroupIndex
  where
    applySubgroupIndex [Fact _ [h,g] _ _, Fact _ [g2,nStr] _ _, Fact _ [h2,mStr] _ _]
      | g == g2 && h == h2 =
        case (safeRead nStr, safeRead mStr) of
          (Right n, Right m) -> 
            if m > 0 && n `mod` m == 0
            then [TOFact (fact "index" [h,g,show (n `div` m)])]
            else []
          _ -> []
    applySubgroupIndex _ = []

-- Coset action theorem: G acts transitively on cosets of H with index n
cosetAction :: Theorem
cosetAction = Theorem "CosetAction"
  (Template [fact "index" ["H","G","n"]])
  applyCosetAction
  where
    applyCosetAction [Fact _ [h,g,nStr] _ _] =
      [TOFact (fact "transitiveAction" [g,nStr])]
    applyCosetAction _ = []

-- Simple group action theorem: if G is simple and has n_p > 1 Sylow p-subgroups, it embeds in A_{n_p}
simpleGroupAction :: Theorem
simpleGroupAction = Theorem "EmbedsIntoSnBySylowAction"
  (Template [fact "numSylow" ["p","G","n_p"], fact "simple" ["G"]])
  applySimpleGroupAction
  where
    applySimpleGroupAction [Fact _ [_,g,npStr] _ _, Fact _ [g2] _ _]
      | g == g2 =
           case safeRead npStr of
             (Right n) -> if n > 1 && n <= 20
                         then let sn = "S" ++ npStr
                              in [TOFact (fact "embedsInSym" [g, sn])]
                         else []
             _ -> []
    applySimpleGroupAction _ = []

-- Multiple Sylows theorem: if num_sylow(p,G,n) where n > 1, then more_than_one_sylow(p,G)
multipleSylows :: Theorem
multipleSylows = Theorem "MultipleSylows"
  (Template [fact "numSylow" ["p","G","n"]])
  applyMultipleSylows
  where
    applyMultipleSylows [Fact _ [p,g,nStr] _ _] =
      case safeRead nStr :: ProverResult Integer of
        (Right n) -> if n > 1
                    then [TOFact (fact "moreThanOneSylow" [p,g])]
                    else []
        _ -> []
    applyMultipleSylows _ = []

-- Alternating order theorem: alternating_group(A,n) implies order(A, n!/2)
alternatingOrder :: Theorem
alternatingOrder = Theorem "AlternatingOrder"
  (Template [fact "alternatingGroup" ["A","n"]])
  applyAlternatingOrder
  where
    applyAlternatingOrder [Fact _ [a,nStr] deps _] =
         case safeRead nStr :: ProverResult Integer of
           (Right n) -> if n >= 1 && n <= 20  -- use Math.factorial bounds
                       then case factorial n of
                              Right fact_n ->
                                let order = fact_n `div` 2
                                    out = [TOFact (fact "order" [a, show order])]
                                in out
                              Left _ -> []
                       else []
           _ -> []
    applyAlternatingOrder _ = []

-- Normal subgroup implies not simple: normal(H,G) and order(H,k) and k > 1 implies not_simple(G)
normalSubgroupNotSimple :: Theorem
normalSubgroupNotSimple = Theorem "NormalSubgroupNotSimple"
  (Template [fact "normal" ["H","G"], fact "order" ["H","k"], fact "order" ["G","n"]])
  applyNormalSubgroupNotSimple
  where
    applyNormalSubgroupNotSimple [Fact _ [h,g] _ _, Fact _ [h2,kStr] _ _, Fact _ [g2,nStr] _ _]
      | h == h2 && g == g2 =
        case (safeRead kStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
          (Right k, Right n) -> if k > 1 && k < n  -- proper nontrivial normal subgroup
                               then [TOFact (fact "notSimple" [g])]
                               else []
          _ -> []
    applyNormalSubgroupNotSimple _ = []

-- Possible max intersections: when there are multiple Sylow p-subgroups, 
-- their pairwise intersections can have order 1, p, p^2, ..., up to p^(k-1)
possibleMaxIntersections :: Theorem
possibleMaxIntersections = Theorem "PossibleMaxIntersections"
  (Template [fact "moreThanOneSylow" ["p","G"], fact "sylowOrder" ["G","p","pk"]])
  applyPossibleMaxIntersections
  where
    applyPossibleMaxIntersections [Fact _ [pStr,g] _ _, Fact _ [g2,p2Str,pkStr] _ _]
      | g == g2 && pStr == p2Str =
        case (safeRead pStr :: ProverResult Integer, safeRead pkStr :: ProverResult Integer) of
          (Right p, Right pk) -> 
            let possibleOrders = takeWhile (< pk) (iterate (* p) 1)  -- [1, p, p^2, ..., p^(k-1)]
                intersectionFacts = [fact "maxSylowIntersection" [g, pStr, show order] | order <- possibleOrders]
            in case intersectionFacts of
                 [] -> []
                 [single] -> [TOFact single]
                 multiple -> [TODisj multiple]
          _ -> []
    applyPossibleMaxIntersections _ = []

-- Intersection of Sylows: if max intersection is p^k, create two Sylow subgroups and their intersection
intersectionOfSylows :: Theorem
intersectionOfSylows = Theorem "IntersectionOfSylows"
  (Template [fact "maxSylowIntersection" ["G","p","pk"]])
  applyIntersectionOfSylows
  where
    applyIntersectionOfSylows [Fact _ [g,pStr,pkStr] _ _] =
      let p1 = "P1"  -- First Sylow subgroup
          p2 = "P2"  -- Second Sylow subgroup  
          inter = "I1"  -- Their intersection
      in [TOFact (fact "sylowPSubgroup" [p1, pStr, g]),
          TOFact (fact "sylowPSubgroup" [p2, pStr, g]),
          TOFact (fact "intersection" [p1, p2, inter]),
          TOFact (fact "order" [inter, pkStr])]
    applyIntersectionOfSylows _ = []

-- Normalizer equals group implies normal: if normalizer(G,H,G) then normal(H,G)
normalizerImpliesNormal :: Theorem
normalizerImpliesNormal = Theorem "NormalizerImpliesNormal"
  (Template [fact "normalizer" ["G","H","G"], fact "order" ["G","n"]])
  applyNormalizerImpliesNormal
  where
    applyNormalizerImpliesNormal [Fact _ [g1,h,g2] _ _, Fact _ [g3,nStr] _ _]
      | g1 == g2 && g2 == g3 =  -- normalizer(G,H,G) and order(G,n)
        [TOFact (fact "normal" [h,g1])]
    applyNormalizerImpliesNormal _ = []

-- Normalizer of Sylow intersection: creates normalizer with possible orders
normalizerSylowIntersection :: Theorem
normalizerSylowIntersection = Theorem "NormalizerSylowIntersection"
  (Template [fact "sylowPSubgroup" ["P","p","G"], 
             fact "sylowPSubgroup" ["Q","p","G"], 
             fact "intersection" ["P","Q","R"], 
             fact "order" ["R","pl"], 
             fact "sylowOrder" ["G","p","pk"], 
             fact "order" ["G","n"]])
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
                            orderFacts = [fact "order" [normalizer_name, show d] | d <- validOrders]
                        in [TOFact (fact "normalizer" [g1, r, normalizer_name]),
                            TOFact (fact "subgroup" [normalizer_name, g1])] ++
                           (case orderFacts of
                              [] -> []
                              [single] -> [TOFact single]
                              multiple -> [TODisj multiple])
                      Left _ -> []
            else []
          _ -> []
    applyNormalizerSylowIntersection _ = []

-- Rule out impossible normalizer orders: if normalizer forces unique Sylow subgroup, contradiction
normalizerOrderContradiction :: Theorem
normalizerOrderContradiction = Theorem "NormalizerOrderContradiction"
  (Template [fact "normalizer" ["G","H","N"], fact "order" ["N","k"], fact "order" ["G","n"]])
  applyNormalizerOrderContradiction
  where
    applyNormalizerOrderContradiction [Fact _ [g1,h,n1] _ _, Fact _ [n2,kStr] _ _, Fact _ [g2,nStr] _ _]
      | g1 == g2 && n1 == n2 =
        case (safeRead kStr :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
          (Right k, Right n) ->
            -- If normalizer has small index, we get embedding into small alternating group
            let index = n `div` k
            in if index > 1 && index <= 4  -- Small index forces small alternating group
               then [TOFact (fact "subgroup" [g1, "A"]),
                     TOFact (fact "alternatingGroup" ["A", show index]),
                     TOFact (fact "divides" [show n, 
                                        case factorial index of
                                          Right fact_n -> show (fact_n `div` 2)
                                          Left _ -> "1"])]
               else []
          _ -> []
    applyNormalizerOrderContradiction _ = []

-- Compatibility shim: convert legacy is(G, Sn) facts into embedsInSym(G, Sn)
convertIsToEmbedsInSym :: Theorem
convertIsToEmbedsInSym = Theorem "ConvertIsToEmbedsInSym"
  (Template [fact "is" ["G","Sn"]])
  applyConvert
  where
    applyConvert [Fact _ [g, sn] _ _] = [TOFact (fact "embedsInSym" [g, sn])]
    applyConvert _ = []

-- Enhanced counting for prime-order Sylow subgroups: when Sylow p-subgroups have prime order p, 
-- they intersect trivially, giving (p-1) * num_sylows elements of order p
primeOrderCounting :: Theorem
primeOrderCounting = Theorem "PrimeOrderCounting"
  (Template [fact "numSylow" ["p","G","n"], fact "sylowOrder" ["G","p","p"], fact "order" ["G","total"]])
  applyPrimeOrderCounting
  where
    applyPrimeOrderCounting [Fact _ [pStr,g1,nStr] _ _, Fact _ [g2,p2Str,p3Str] _ _, Fact _ [g3,totalStr] _ _]
      | g1 == g2 && g2 == g3 && pStr == p2Str && p2Str == p3Str =
        case (safeRead pStr :: ProverResult Integer, 
              safeRead nStr :: ProverResult Integer, 
              safeRead totalStr :: ProverResult Integer) of
          (Right p, Right n, Right total) ->
            if n > 1  -- Multiple Sylow subgroups
            then let elementsOfOrderP = (p - 1) * n
                 in [TOFact (fact "orderPkLowerBound" [g1, pStr, show elementsOfOrderP])]
            else []
          _ -> []
    applyPrimeOrderCounting _ = []



-- Counting contradiction using order p^k lower bounds
orderPkCountingContradiction :: Theorem
orderPkCountingContradiction = Theorem "OrderPkCountingContradiction"
  (Template [fact "orderPkLowerBound" ["G","p1","n1"], fact "orderPkLowerBound" ["G","p2","n2"], fact "order" ["G","total"]])
  applyOrderPkCountingContradiction
  where
    applyOrderPkCountingContradiction [Fact _ [g1,p1Str,n1Str] _ _, Fact _ [g2,p2Str,n2Str] _ _, Fact _ [g3,totalStr] _ _]
      | g1 == g2 && g2 == g3 && p1Str /= p2Str =  -- Different primes
        case (safeRead n1Str :: ProverResult Integer, 
              safeRead n2Str :: ProverResult Integer,
              safeRead totalStr :: ProverResult Integer) of
          (Right n1, Right n2, Right total) ->
            if n1 + n2 + 1 > total  -- +1 for identity element, too many elements
            then [TOFact (fact "false" [])]
            else []
          _ -> []
    applyOrderPkCountingContradiction _ = []

-- Simple contradiction theorem (simple ∧ not_simple → false)
simpleNotSimple :: Theorem
simpleNotSimple = Theorem "SimpleNotSimple"
  (Template [fact "simple" ["G"], fact "not_simple" ["G"]])
  applySimpleNotSimple
  where
    applySimpleNotSimple [Fact _ [g1] _ _, Fact _ [g2] _ _]
      | g1 == g2 = [TOFact (fact "false" [])]
      | otherwise = []
    applySimpleNotSimple _ = []



-- if a group G has a subgroup H of index 2, and G embeds in Sn, then H might be An
possibleAn :: Theorem
possibleAn = Theorem "possibleAn"
  (Template [fact "index" ["H","G","2"], fact "is" ["G", "Sn"]])
  applyPossibleAn
  where
    applyPossibleAn facts@[Fact _ [h, g, "2"] _ _, Fact _ [g2, sn] _ _]
      | g == g2 =
          let traceMsg = "possibleAn triggered for H=" ++ h ++ ", G=" ++ g ++ ", sn=" ++ sn ++ ". Facts: " ++ show facts
          in trace traceMsg $
          let nStr = drop 1 sn -- "S4" -> "4"
          in case (safeRead nStr :: ProverResult Integer) of
            Right n -> if n >= 2
                       then let out = [TOFact (fact "is" [h, "A" ++ nStr]),
                                       TOFact (fact "alternatingGroup" [h, nStr])]
                            in trace ("  -> Produced: " ++ show out) out
                       else trace "  -> Condition n >= 2 not met." []
            _ -> trace "  -> Failed to parse n from sn." []
    applyPossibleAn _ = []


-- Standard theorem collection
standardTheorems :: [Theorem]
standardTheorems = 
  [ sylowTheorem
  , uniqueSylowContradiction  
  , sylowPSubgroupGeneration
  , actionOnSylowSubgroups
  , actionEmbedsInSym
  , convertIsToEmbedsInSym
  , orderDividesSym
  , orderDividesAlt
  , sylowNormalizerIndex
  , normalizerAutBoundPrime
  , countOrderPkElements
  , countingContradiction
  , lagrangeTheorem
  , divisibilityContradiction
  , alternatingGroupSimple
  , subgroupIndex
  , cosetAction
  , simpleGroupAction
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
  , possibleAn
  ]

-- New: If there are n_p Sylow p-subgroups of G, then index(N_G(P)) = n_p
-- We record index(N,P) = n_p as a fact, and if order(G,n) and order(P,p) with p prime, we can derive order of normalizer divides n with index n_p
sylowNormalizerIndex :: Theorem
sylowNormalizerIndex = Theorem "SylowNormalizerIndex"
  (Template [fact "numSylow" ["p","G","n_p"], fact "sylowPSubgroup" ["P","p","G"]])
  applySylowNormalizerIndex
  where
    applySylowNormalizerIndex [Fact _ [pStr,g,npStr] _ _, Fact _ [p2Str,p3Str,g2] _ _]
      | g == g2 && pStr == p2Str && p2Str == p3Str =
          [TOFact (fact "index" ["N","G", npStr]),
           TOFact (fact "subgroup" ["N","G"]),
           TOFact (fact "normalizer" [g, "P", "N"])]
    applySylowNormalizerIndex _ = []

-- New: If P is a Sylow p-subgroup of prime order p and n_p > 1, then n_p | (p-1)
-- Encoded as: when sylowOrder(G,p,p) and numSylow(p,G,n) with n>1, then divides(n, p-1)
normalizerAutBoundPrime :: Theorem
normalizerAutBoundPrime = Theorem "NormalizerAutBoundPrime"
  (Template [fact "sylowOrder" ["G","p","p"], fact "numSylow" ["p","G","n"], fact "order" ["G","N"]])
  applyAutBound
  where
    applyAutBound [Fact _ [g1,pStr1,_] _ _, Fact _ [pStr2,g2,nStr] _ _, Fact _ [g3,nTotalStr] _ _]
      | g1 == g2 && g2 == g3 && pStr1 == pStr2 =
          case (safeRead pStr1 :: ProverResult Integer, safeRead nStr :: ProverResult Integer) of
            (Right p, Right n) -> if n > 1
                                  then [TOFact (fact "divides" [nStr, show (p-1)])]
                                  else []
            _ -> []
    applyAutBound _ = []