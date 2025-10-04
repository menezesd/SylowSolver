-- | Standard theorems for the Sylow solver
module Theorems where

import Data.Set (fromList)
import qualified Data.Set as S
-- Removed unused IORef / unsafePerformIO imports after abandoning memoization.
import Types
  ( Fact(..)
  , Pred(..)
  , Value(..)
  , TPattern(..)
  , TTemplate(..)
  , ThmOut(..)
  , Theorem(..)
  , Provenance(..)
  , mkFactP
  , parseSymGroup
  , parseAltGroup
  , vpFixed, vpVar, vpAny
  , mkTPattern, mkTTemplate
  , mkTheoremT
  )
import Math
import Errors
import Debug.Trace (trace)
import DebugLog (dtrace)

-- Helper function for divisors (from sylow2.py)
divisors :: Integer -> [Integer] 
divisors n 
  | n <= 0 = []
  | otherwise = 
      let r = floor (sqrt (fromIntegral n))
          divs = [i | i <- [1..r], n `mod` i == 0] ++ 
                 [n `div` i | i <- [1..r], n `mod` i == 0, n `div` i /= i]
      in divs

-- Sylow's theorem - generates constraints on number of Sylow p-subgroups
sylowTheorem :: Theorem
sylowTheorem = mkTheoremT "SylowDivisibilityCongruence" 5
  (mkTTemplate [ mkTPattern "group" [vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySylow
  where
    applySylow facts@[gFact@(Fact _ [Sym g] _ _), orderFact@(Fact _ [g2Val, Nat nVal] _ _)]
      | g2Val == Sym g =
          case primeFactorization nVal of
            Left _ -> [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "SylowDivisibilityCongruence" facts Nothing Nothing)))]
            Right factors -> 
              let factorsInt = [ (fromIntegral p :: Int, k) | (p,k) <- factors ]
              in concatMap (perFactor g (fromInteger nVal) facts) factorsInt
    applySylow _ = []

    perFactor :: String -> Int -> [Fact] -> (Int, Int) -> [ThmOut]
    perFactor g n facts (pInt,k) =
      let p  = fromIntegral pInt :: Integer
          pkInteger = p ^ fromIntegral k
          pk = fromInteger pkInteger :: Int
          mInteger  = toInteger n `div` pkInteger
          divisors = case allDivisors mInteger of
                       Left _ -> []
                       Right ds -> ds
          validCounts = [fromInteger d | d <- divisors, d `mod` p == 1]
          countFacts = case validCounts of
                         []      -> [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "SylowDivisibilityCongruence" facts Nothing Nothing)))]
                         [d]     -> [TOFact (mkFactP PNumSylow [Nat (fromIntegral pInt), Sym g, Nat (fromIntegral d)])]
                         ds      -> [TODisj [ mkFactP PNumSylow [Nat (fromIntegral pInt), Sym g, Nat (fromIntegral d)] | d <- ds]]
          sylowTag = "S" ++ show p ++ "_" ++ show pk
          orderFacts = [ TOFact (mkFactP PSylowOrder [Sym g, Nat (fromIntegral pInt), Nat (fromIntegral pk)])
                       , TOFact (mkFactP PSylowPSubgroup [Sym sylowTag, Nat (fromIntegral pInt), Sym g])
                       , TOFact (mkFactP POrder [Sym sylowTag, Nat (fromIntegral pk)])
                       ]
          outs = countFacts ++ orderFacts
          debugMsg = "applySylow g=" ++ g ++ " p=" ++ show pInt ++ " pk=" ++ show pk ++ " m=" ++ show mInteger ++ " validCounts=" ++ show validCounts
      in dtrace debugMsg outs

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
    applyUniqueSylow [Fact _ [Sym g] _ _, _, Fact _ [_, _, pkVal] _ _, Fact _ [_, nVal] _ _] =
      case (pkVal, nVal) of
        (Nat pk, Nat n) -> if pk > 1 && pk < n then [TOFact (mkFactP PNotSimple [Sym g])] else []
        _ -> []
    applyUniqueSylow _ = []

-- Removed redundant sylowPSubgroupGeneration theorem.
-- Rationale: "sylowTheorem" already produces a canonical Sylow subgroup fact and its order.
-- Keeping this secondary generator caused explosive duplicate generation loops.
-- If reintroduction is ever needed, ensure it checks for existing subgroup/order facts first.



-- Action on Sylow subgroups: if n_p > 1, G acts on them.

-- Embedding in alternating group: if G is simple and has n_p > 1 Sylow p-subgroups, 
-- then G embeds as a subgroup in A_{n_p} via the conjugation action
embedInAlternating :: Theorem
embedInAlternating = mkTheoremT "EmbedInAlternating" 15
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"]
               , mkTPattern "simple" [vpVar "G"]
               ])
  applyEmbedInAlternating
  where
    -- Revised semantics: produce an abstract embedding predicate embedInAlt(G, A_n)
    -- (later a separate theorem can translate embedInAlt + alternatingGroup + order facts
    -- into subgroup/divisibility when justified). This avoids premature Lagrange explosions.
    -- Gate at n_p >= 5 (so A_n is simple and classical action more controlled).
    applyEmbedInAlternating [Fact _ [_, gVal, npVal] _ _, Fact _ [g2Val] _ _]
      | gVal == g2Val =
          case npVal of
            Nat np | np >= 5 -> 
              let altName = Sym ("A_" ++ show np)
              in if gVal == altName
                   then []  -- avoid degenerate self embedding that led to subgroup(A_5, A_5)
                   else [ TOFact (mkFactP PEmbedInAlt [gVal, altName])
                        , TOFact (mkFactP PAlternatingGroup [altName, Nat np])
                        ]
            _ -> []
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

-- Convert an abstract alternating embedding to a subgroup relationship when
-- we have both orders and |G| divides |A_n| (syntactic safe check: factorial bound).
-- This prevents the earlier unsound immediate use of Lagrange on fabricated subgroups.
embedAltToSubgroup :: Theorem
embedAltToSubgroup = mkTheoremT "EmbedAltToSubgroup" 12
  (mkTTemplate [ mkTPattern "embedInAlt" [vpVar "G", vpVar "A"]
               , mkTPattern "alternatingGroup" [vpVar "A", vpVar "n"]
               , mkTPattern "order" [vpVar "G", vpVar "m"]
               , mkTPattern "order" [vpVar "A", vpVar "k"]
               ])
  applyEmbedAltToSubgroup
  where
    applyEmbedAltToSubgroup [Fact _ [gVal,aVal] _ _, Fact _ [a2Val,nVal] _ _, Fact _ [g2Val,mVal] _ _, Fact _ [a3Val,kVal] _ _]
      | aVal == a2Val && a2Val == a3Val && gVal == g2Val =
          case (gVal,aVal,nVal,mVal,kVal) of
            (Sym g, Sym a, Nat n, Nat m, Nat k) ->
              if k >= m then [ TOFact (mkFactP PSubgroup [Sym g, Sym a])
                             , TOFact (mkFactP PDivides [Nat m, Nat k])
                             ] else []
            _ -> []
    applyEmbedAltToSubgroup _ = []

-- Derive faithfulAction(G,n): require a coset action plus index(H,G,n) and strict order drop |H| < |G|, so kernel can't be all of G.
faithfulCosetAction :: Theorem
faithfulCosetAction = mkTheoremT "FaithfulCosetAction" 18
  (mkTTemplate [ mkTPattern "cosetAction" [vpVar "G", vpVar "H", vpVar "n"]
               , mkTPattern "index" [vpVar "H", vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "G", vpVar "m"]
               , mkTPattern "order" [vpVar "H", vpVar "h"]
               ])
  applyFaithfulCoset
  where
    applyFaithfulCoset [Fact _ [g1,h1,n1] _ _, Fact _ [h2,g2,n2] _ _, Fact _ [g3,mVal] _ _, Fact _ [h3,hVal] _ _]
      | g1 == g2 && g1 == g3 && h1 == h2 && h1 == h3 && n1 == n2 =
          case (g1,h1,n1,mVal,hVal) of
            (Sym g, Sym h, Nat n, Nat m, Nat hOrder) ->
              if hOrder < m && n > 1 then [TOFact (mkFactP PFaithfulAction [Sym g, Nat n])] else []
            _ -> []
    applyFaithfulCoset _ = []

-- Guarded simple group action embedding: with faithfulAction(G,n), simple(G), order(G,m) and m <= n!, produce embedding into alternating when safe.
simpleGroupActionFaithful :: Theorem
simpleGroupActionFaithful = mkTheoremT "SimpleGroupActionFaithful" 22
  (mkTTemplate [ mkTPattern "faithfulAction" [vpVar "G", vpVar "n"]
               , mkTPattern "simple" [vpVar "G"]
               , mkTPattern "order" [vpVar "G", vpVar "m"]
               ])
  applySimpleActionFaithful
  where
    applySimpleActionFaithful [Fact _ [gVal,nVal] _ _, Fact _ [g2Val] _ _, Fact _ [g3Val,mVal] _ _]
      | gVal == g2Val && gVal == g3Val =
          case (gVal,nVal,mVal) of
            (Sym g, Nat n, Nat m) | n > 1 ->
              case factorial (fromIntegral n) of
                Right factN ->
                  let altName = Sym ("A_" ++ show n)
                      safeAlt = n < 5 || factN >= 2 && fromIntegral m <= factN `div` 2
                  in if fromIntegral m <= factN && safeAlt
                        then [ TOFact (mkFactP PEmbedInAlt [Sym g, altName])
                             , TOFact (mkFactP PAlternatingGroup [altName, Nat (fromIntegral n)])
                             ]
                        else []
                Left _ -> []
            _ -> []
    applySimpleActionFaithful _ = []

-- Safe symmetric embedding divisibility: only produce divides fact when it really holds
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
          Right factM | factM `mod` n == 0 -> [TOFact (mkFactP PDivides [Nat n, Nat factM])]
          _ -> []
        _ -> []
    applySymDivision _ = []

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
    applyCountingContradiction facts@[fact1@(Fact _ [_,p1Val,n1Val] _ _), 
                                     fact2@(Fact _ [_,p2Val,n2Val] _ _), 
                                     fact3@(Fact _ [_,nVal] _ _)] =
      case (p1Val, p2Val, n1Val, n2Val, nVal) of
        (Nat p1, Nat p2, Nat n1, Nat n2, Nat n) ->
          if p1 /= p2 && n1 + n2 + 1 > n  -- +1 for identity element
          then [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "CountingContradiction" facts Nothing Nothing)))]
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
    applyDivisibilityContradiction [divideFact@(Fact _ [mVal,nVal] _ _)] =
         case (mVal, nVal) of
           (Nat m, Nat n) -> 
             if n `mod` m /= 0
             then [TOFact (Fact PFalse [] (fDeps divideFact) (Just (ProvTheorem { thmName = "DivisibilityContradiction", parentFacts = [divideFact], fromDisj = Nothing, provSubs = Nothing })))]
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
multipleSylows = mkTheoremT "MultipleSylows" 1
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n_p"] ])
  applyMultipleSylows
  where
    applyMultipleSylows [Fact _ [pVal, gVal, npVal] _ _] =
      case npVal of
        Nat np | np > 1 -> [TOFact (mkFactP PMoreThanOneSylow [pVal, gVal])]
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
            let -- Exclude the trivial intersection order 1; start from p up to < pk
                possibleOrders = takeWhile (< pk) (iterate (* p) p)
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

-- If normalizer(G,H,N) and order(N,n) and order(G,n) then normal(H,G)
-- Mirrors Python's normalizer_everything_implies_normal (which uses size equality rather than literal N = G)
-- Refined: also require order(H,k) with k>1 to avoid repeatedly deriving normal(1,G)
-- This prunes a large number of redundant applications when the intersection subgroup has order 1.
normalizerEqualityImpliesNormal :: Theorem
normalizerEqualityImpliesNormal = mkTheoremT "NormalizerEqualityImpliesNormal" 6
  (mkTTemplate [ mkTPattern "normalizer" [vpVar "G", vpVar "H", vpVar "N"]
               , mkTPattern "order" [vpVar "N", vpVar "n"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "H", vpVar "k"]
               ])
  applyNormalizerEqualityImplies
  where
    applyNormalizerEqualityImplies [Fact _ [gVal,hVal,nVal] _ _, Fact _ [n2Val,nOrderVal] _ _, Fact _ [g2Val,gOrderVal] _ _, Fact _ [h2Val,kVal] _ _]
      | gVal == g2Val && nOrderVal == gOrderVal && nVal == n2Val && hVal == h2Val =
          case (hVal, gVal, kVal) of
            (Sym h, Sym g, Nat k) | k > 1 -> [TOFact (mkFactP PNormal [Sym h, Sym g])]
            _ -> []
    applyNormalizerEqualityImplies _ = []

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
    applyNormalizerSylowIntersection facts@[Fact _ [p1Val,pStr1Val,g1Val] _ _, 
                                            Fact _ [p2Val,pStr2Val,g2Val] _ _, 
                                            Fact _ [p1'Val,p2'Val,rVal] _ _, 
                                            Fact _ [r'Val,plVal] _ _, 
                                            Fact _ [g3Val,pStr3Val,pkVal] _ _, 
                                            Fact _ [g4Val,nVal] _ _]
      | g1Val == g2Val && g2Val == g3Val && g3Val == g4Val
        && pStr1Val == pStr2Val && pStr2Val == pStr3Val
        && p1Val == p1'Val && p2Val == p2'Val && rVal == r'Val =
          case (g1Val, rVal, plVal, pkVal, nVal) of
            (Sym g1, Sym r, Nat pl, Nat pk, Nat n) ->
              -- Require a nontrivial intersection (pl > 1) in addition to pk > pl.
              -- The pl = 1 cases were generating a flood of identical normalizer facts
              -- across many Sylow number disjunction branches, bloating the search.
              if pk > pl && pl > 1 then
                let normalizer_name = "N1"
                    -- Recover prime p from the Sylow subgroup second argument (pStr1Val)
                    pMaybe = case pStr1Val of { Nat p -> Just p; _ -> Nothing }
                in case pMaybe of
                     Nothing -> []
                     Just p ->
                       let validOrders = [d | d <- [1..n], d `mod` pk == 0, d > pk, n `mod` d == 0]
                           orderFacts = [mkFactP POrder [Sym normalizer_name, Nat d] | d <- validOrders]
                           mainFacts = [ TOFact (mkFactP PNormalizer [Sym g1, Sym r, Sym normalizer_name])
                                       , TOFact (mkFactP PSubgroup [Sym normalizer_name, Sym g1])
                                       , TOFact (mkFactP PNormalizerOfSylowIntersection [Nat p, Sym g1, Sym normalizer_name])
                                       ]
                           extraFacts = case orderFacts of
                                          [] -> []
                                          [single] -> [TOFact single]
                                          multiple -> [TODisj multiple]
                       in mainFacts ++ extraFacts
              else []
            _ -> []
    applyNormalizerSylowIntersection _ = []

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
    applyOrderPkCountingContradiction facts@[fact1@(Fact _ [g1Val,p1Val,n1Val] _ _), fact2@(Fact _ [g2Val,p2Val,n2Val] _ _), fact3@(Fact _ [g3Val,totalVal] _ _)]
      | g1Val == g2Val && g2Val == g3Val && p1Val /= p2Val =
        case (n1Val, n2Val, totalVal) of
          (Nat n1, Nat n2, Nat total) ->
            if n1 + n2 + 1 > total
            then [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "OrderPkCountingContradiction" facts Nothing Nothing)))]
            else []
          _ -> []
    applyOrderPkCountingContradiction _ = []

-- Simple contradiction theorem (simple ∧ not_simple → false)
simpleNotSimple :: Theorem
simpleNotSimple = mkTheoremT "SimpleNotSimple" 2
  (mkTTemplate [ mkTPattern "simple" [vpVar "G"], mkTPattern "not_simple" [vpVar "G"] ])
  applySimpleNotSimple
  where
    applySimpleNotSimple facts@[fact1@(Fact _ [g1] _ _), fact2@(Fact _ [g2] _ _)]
      | g1 == g2 = [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "SimpleNotSimple" facts Nothing Nothing)))]
      | otherwise = []
    applySimpleNotSimple _ = []

-- A group cannot have two different orders
-- uniqueOrderTheorem :: Theorem
-- uniqueOrderTheorem = mkTheoremT "UniqueOrder" 1
--   (mkTTemplate [ mkTPattern "order" [vpVar "G", "n1"]
--                , mkTPattern "order" [vpVar "G", "n2"]
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
  -- , sylowPSubgroupGeneration  -- DISABLED: Redundant with sylowTheorem which already generates subgroups
  , embedInAlternating
  , embedAltToSubgroup
  -- legacy conversions removed
  , orderDividesSym
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
  , faithfulCosetAction        -- new: derive faithfulAction from core-free coset action pattern
  , simpleGroupActionFaithful  -- new: guarded replacement for simpleGroupActionAlt
  -- , simpleGroupActionAlt  -- legacy parity attempt (disabled)
  -- , simpleGroupAction  -- DISABLED: This theorem is incorrect and causes false contradictions
  , multipleSylows
  , alternatingOrder
  , normalSubgroupNotSimple
  , possibleMaxIntersections
  , intersectionOfSylows
  , normalizerImpliesNormal
  , normalizerEqualityImpliesNormal
  , normalizerEverythingImpliesNormal -- parity with Python normalizer_everything_implies_normal
  , normalizerSylowIntersection
  , primeOrderCounting
  , orderPkCountingContradiction
  , simpleNotSimple
  , ruleOutMaxIntersections  -- REFINED: Now only applies to non-trivial intersections
  , ruleOutNormalizerOrder
  , singleSylowNotSimple      -- new
  , primeMinimalIndexNormal   -- new
  , index2Normal              -- new
  , normalSubgroupToNotSimple -- new
  , sylowCountNarrowDivides   -- new
  , sylowCountNarrowCongruence -- new
  , sylowCountDividesUpper     -- new
  , sylowCountCongruence       -- new
  , sylowNormalizerOrder       -- new
  , hallSubgroupDetection      -- new
  , hallSubgroupNormalInSimple -- new
  , sylowUniquenessFromDivCong -- new
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

-- Rule out max intersections: From Python rule_rule_out_max_intersections
-- When we have numSylow(p,G,np), maxSylowIntersection(G,p,p^l), sylowPOrder(G,p,p^k)  
-- If l < k (non-trivial intersection) and np ≢ 1 (mod p^k/p^l), then contradiction
-- This theorem only applies to proper non-trivial intersections where l > 0 and l < k
ruleOutMaxIntersections :: Theorem
ruleOutMaxIntersections = mkTheoremT "RuleOutMaxIntersections" 25
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "np"]
               , mkTPattern "maxSylowIntersection" [vpVar "G", vpVar "p", vpVar "pl"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               ])
  applyRuleOutMaxIntersections
  where
    applyRuleOutMaxIntersections facts@[Fact _ [pVal,gVal,npVal] _ _, 
                                        Fact _ [g2Val,p2Val,plVal] _ _, 
                                        Fact _ [g3Val,p3Val,pkVal] _ _]
      | gVal == g2Val && g2Val == g3Val && pVal == p2Val && p2Val == p3Val =
          case (pVal, npVal, plVal, pkVal) of
            (Nat p, Nat np, Nat pl, Nat pk) -> 
              -- Only apply if: 
              -- 1. We have a proper non-trivial intersection: pl > 1 and pl < pk
              -- 2. pk is divisible by pl (proper power relationship)  
              -- 3. The normalizer condition fails: np ≢ 1 (mod pk/pl)
              if pl > 1 && pl < pk && pk `mod` pl == 0 && np `mod` (pk `div` pl) /= 1
              then [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "RuleOutMaxIntersections" facts Nothing Nothing)))]
              else []
            _ -> []
    applyRuleOutMaxIntersections _ = []

-- Rule out normalizer of intersection order: From Python rule_rule_out_normalizer_of_intersection_order  
-- When normalizerOfSylowIntersection(p,G,T) and order(T,k), if T has only one Sylow p-subgroup, contradiction
ruleOutNormalizerOrder :: Theorem
ruleOutNormalizerOrder = mkTheoremT "RuleOutNormalizerOrder" 25
  (mkTTemplate [ mkTPattern "normalizerOfSylowIntersection" [vpVar "p", vpVar "G", vpVar "T"]
               , mkTPattern "order" [vpVar "T", vpVar "k"]
               ])
  applyRuleOutNormalizerOrder
  where
    -- Heuristic rule (mirrors Python intent): If the normalizer T of a Sylow p-intersection
    -- has order k where k is itself a pure power of p (k = p^a) and a > 0, then T has a unique
    -- Sylow p-subgroup. But by construction T normalizes an intersection coming from
    -- multiple Sylow p-subgroups of G. That forces a contradiction because inside T the
    -- Sylow p-subgroups must be conjugate and unique.
    applyRuleOutNormalizerOrder facts@[Fact _ [pVal,_gVal,tVal] _ _, 
                                       Fact _ [t2Val,kVal] _ _]
      | tVal == t2Val =
          case (pVal, kVal) of
            (Nat p, Nat k) ->
              if p > 1 && k > 1 && isPurePowerOf p k then
                [TOFact (Fact PFalse [] (fromList []) (Just (ProvTheorem "RuleOutNormalizerOrder" facts Nothing Nothing)))]
              else []
            _ -> []
    applyRuleOutNormalizerOrder _ = []

    isPurePowerOf :: Integer -> Integer -> Bool
    isPurePowerOf p n = go 1
      where
        go acc | acc == n = True
               | acc > n = False
               | otherwise = go (acc * p)

-- Single Sylow subgroup implies not simple if group order not a pure p-power (Python: single_sylow_not_simple)
singleSylowNotSimple :: Theorem
singleSylowNotSimple = mkTheoremT "SingleSylowNotSimple" 8
  (mkTTemplate [ mkTPattern "sylowPSubgroup" [vpVar "P", vpVar "p", vpVar "G"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpFixed (Nat 1)]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySingleSylowNotSimple
  where
    applySingleSylowNotSimple [Fact _ [_,pVal,gVal] _ _, Fact _ [p2Val,g2Val,_] _ _, Fact _ [g3Val,nVal] _ _]
      | pVal == p2Val && gVal == g2Val && gVal == g3Val =
          case (pVal,nVal,gVal) of
            (Nat p, Nat n, Sym g) -> if n > 1 && not (isPurePowerOfLocal p n)
                                        then [TOFact (mkFactP PNotSimple [Sym g])]
                                        else []
            _ -> []
    applySingleSylowNotSimple _ = []

    isPurePowerOfLocal :: Integer -> Integer -> Bool
    isPurePowerOfLocal p n = go 1
      where
        go acc | acc == n = True
               | acc > n = False
               | otherwise = go (acc * p)

-- Prime minimal index normality: index(H,G,p), order(G,n)=p*m, order(H,m), p smallest prime divisor of n => normal(H,G)
primeMinimalIndexNormal :: Theorem
primeMinimalIndexNormal = mkTheoremT "PrimeMinimalIndexNormal" 10
  (mkTTemplate [ mkTPattern "index" [vpVar "H", vpVar "G", vpVar "p"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               ])
  applyPrimeMinimalIndexNormal
  where
    applyPrimeMinimalIndexNormal [Fact _ [hVal,gVal,pVal] _ _, Fact _ [g2Val,nVal] _ _, Fact _ [h2Val,mVal] _ _]
      | hVal == h2Val && gVal == g2Val =
          case (pVal,nVal,mVal,hVal,gVal) of
            (Nat p, Nat n, Nat m, Sym h, Sym g) ->
              if n == p * m && p > 1 then
                 case primeFactorization n of
                   Right facs -> let primes = [pr | (pr,_) <- facs]
                                     smallest = minimum primes
                                 in if elem p primes && p == smallest
                                       then [TOFact (mkFactP PNormal [Sym h, Sym g])]
                                       else []
                   Left _ -> []
              else []
            _ -> []
    applyPrimeMinimalIndexNormal _ = []

-- Index 2 implies normal immediately (special fast rule)
index2Normal :: Theorem
index2Normal = mkTheoremT "Index2Normal" 4
  (mkTTemplate [ mkTPattern "index" [vpVar "H", vpVar "G", vpFixed (Nat 2)]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "H", vpVar "m"]
               ])
  applyIndex2
  where
    applyIndex2 [Fact _ [hVal,gVal,_] _ _, Fact _ [g2Val,nVal] _ _, Fact _ [h2Val,mVal] _ _]
      | hVal == h2Val && gVal == g2Val =
          case (nVal,mVal,hVal,gVal) of
            (Nat n, Nat m, Sym h, Sym g) -> if n == 2*m then [TOFact (mkFactP PNormal [Sym h, Sym g])] else []
            _ -> []
    applyIndex2 _ = []

-- Normal proper subgroup implies not simple (Python: normal_subgroup_to_not_simple)
normalSubgroupToNotSimple :: Theorem
normalSubgroupToNotSimple = mkTheoremT "NormalSubgroupToNotSimple" 6
  (mkTTemplate [ mkTPattern "normal" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "h"]
               , mkTPattern "order" [vpVar "G", vpVar "g"]
               ])
  applyNormalToNotSimple
  where
    applyNormalToNotSimple [Fact _ [hVal,gVal] _ _, Fact _ [h2Val,hOrder] _ _, Fact _ [g2Val,gOrder] _ _]
      | hVal == h2Val && gVal == g2Val =
          case (hOrder,gOrder,gVal) of
            (Nat h, Nat g, Sym gName) -> if 1 < h && h < g then [TOFact (mkFactP PNotSimple [Sym gName])] else []
            _ -> []
    applyNormalToNotSimple _ = []

-- Narrow Sylow count using divisibility: if numSylow(p,G,n_p) and divides(n_p, d) and d has exactly one positive divisor k satisfying k ≡ 1 (mod p) then force numSylow(p,G,k).
sylowCountNarrowDivides :: Theorem
sylowCountNarrowDivides = mkTheoremT "SylowCountNarrowDivides" 14
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "np"]
               , mkTPattern "divides" [vpVar "np", vpVar "d"]
               ])
  applyNarrowDivides
  where
    applyNarrowDivides [Fact _ [pVal,gVal,npVal] _ _, Fact _ [np2Val,dVal] _ _]
      | npVal == np2Val =
          case (pVal,dVal,gVal) of
            (Nat p, Nat d, Sym g) ->
               if p > 1 && d > 0 then
                 let candidates = [k | k <- divisorsOf d, k `mod` p == 1]
                 in case candidates of
                      [k] -> [TOFact (mkFactP PNumSylow [Nat p, Sym g, Nat k])]
                      _   -> []
               else []
            _ -> []
    applyNarrowDivides _ = []

    divisorsOf n = [d | d <- [1..n], n `mod` d == 0]

-- Narrow Sylow count using congruence and factorial/alternating constraints (light version):
-- If numSylow(p,G,n_p) and divides(n_p, d) AND we already know order(G,m), filter divisors of d that also divide m.
-- If that leaves exactly one k with k ≡ 1 (mod p), enforce it.
sylowCountNarrowCongruence :: Theorem
sylowCountNarrowCongruence = mkTheoremT "SylowCountNarrowCongruence" 16
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "np"]
               , mkTPattern "divides" [vpVar "np", vpVar "d"]
               , mkTPattern "order" [vpVar "G", vpVar "m"]
               ])
  applyNarrowCongruence
  where
    applyNarrowCongruence [Fact _ [pVal,gVal,npVal] _ _, Fact _ [np2Val,dVal] _ _, Fact _ [g2Val,mVal] _ _]
      | npVal == np2Val && gVal == g2Val =
          case (pVal,dVal,mVal,gVal) of
            (Nat p, Nat d, Nat m, Sym g) ->
               if p > 1 && d > 0 then
                  let candidates = [k | k <- divisorsOf d, k `mod` p == 1, m `mod` k == 0]
                  in case candidates of
                       [k] -> [TOFact (mkFactP PNumSylow [Nat p, Sym g, Nat k])]
                       _   -> []
               else []
            _ -> []
    applyNarrowCongruence _ = []

    divisorsOf n = [d | d <- [1..n], n `mod` d == 0]

-- Sylow count divisibility upper bound: from sylowOrder(G,p,p^k) and order(G,n) and numSylow(p,G,r) with n divisible by p^k produce divides(r, n/p^k)
sylowCountDividesUpper :: Theorem
sylowCountDividesUpper = mkTheoremT "SylowCountDividesUpper" 10
  (mkTTemplate [ mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "r"]
               ])
  applySylowDivBound
  where
    applySylowDivBound [Fact _ [gVal,pVal,pkVal] _ _, Fact _ [g2Val,nVal] _ _, Fact _ [p2Val,g3Val,rVal] _ _]
      | gVal == g2Val && g2Val == g3Val && pVal == p2Val =
          case (pVal, pkVal, nVal, rVal) of
            (Nat p, Nat pk, Nat n, Nat r) ->
              if pk > 0 && n `mod` pk == 0 && pk `mod` p == 0 then
                 let q = n `div` pk in [TOFact (mkFactP PDivides [Nat r, Nat q])]
              else []
            _ -> []
    applySylowDivBound _ = []

-- Sylow count congruence: from numSylow(p,G,r) with r>1 produce divides(p, r-1) encoding r ≡ 1 (mod p)
sylowCountCongruence :: Theorem
sylowCountCongruence = mkTheoremT "SylowCountCongruence" 6
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "r"] ])
  applySylowCong
  where
    applySylowCong [Fact _ [pVal,gVal,rVal] _ _] =
      case (pVal,rVal) of
        (Nat p, Nat r) | p > 1 && r > 1 -> [TOFact (mkFactP PDivides [Nat p, Nat (r-1)])]
        _ -> []
    applySylowCong _ = []

-- Derive order of normalizer of a Sylow p-subgroup when we know numSylow and group order and sylow order: |G| = n_p * |N_G(P)|
sylowNormalizerOrder :: Theorem
sylowNormalizerOrder = mkTheoremT "SylowNormalizerOrder" 12
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "np"]
               , mkTPattern "sylowOrder" [vpVar "G", vpVar "p", vpVar "pk"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applySylowNormOrder
  where
    applySylowNormOrder [Fact _ [pVal,gVal,npVal] _ _, Fact _ [g2Val,p2Val,pkVal] _ _, Fact _ [g3Val,nVal] _ _]
      | gVal == g2Val && g2Val == g3Val && pVal == p2Val =
          case (npVal,pkVal,nVal,gVal) of
            (Nat np, Nat pk, Nat n, Sym g) ->
               if np > 0 && pk > 0 && n `mod` pk == 0 && (n `mod` np == 0) then
                  let remDiv = n `div` np
                  in if remDiv `mod` pk == 0 then
                       let normOrder = remDiv in [TOFact (mkFactP POrder [Sym ("N_"++show pVal++"_"++g), Nat normOrder])]
                     else []
               else []
            _ -> []
    applySylowNormOrder _ = []

-- Detect Hall subgroup: if subgroup(H,G) and order(H,h), order(G,n) with gcd(h,n/h)=1 and 1<h<n
hallSubgroupDetection :: Theorem
hallSubgroupDetection = mkTheoremT "HallSubgroupDetection" 10
  (mkTTemplate [ mkTPattern "subgroup" [vpVar "H", vpVar "G"]
               , mkTPattern "order" [vpVar "H", vpVar "h"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               ])
  applyHallDetect
  where
    applyHallDetect [Fact _ [hVal,gVal] _ _, Fact _ [h2Val,hOrder] _ _, Fact _ [g2Val,nOrder] _ _]
      | hVal == h2Val && gVal == g2Val =
          case (hOrder,nOrder,hVal,gVal) of
            (Nat h, Nat n, Sym hS, Sym gS) ->
              if h > 1 && h < n && n `mod` h == 0 && gcd h (n `div` h) == 1 then
                 [TOFact (mkFactP PHallSubgroup [Sym hS, Sym gS, Nat h])]
              else []
            _ -> []
    applyHallDetect _ = []

-- In a simple group, a Hall subgroup (proper nontrivial) must be normal (or yields contradiction). We take route: hallSubgroup(H,G,_) & simple(G) ⇒ normal(H,G)
hallSubgroupNormalInSimple :: Theorem
hallSubgroupNormalInSimple = mkTheoremT "HallSubgroupNormalInSimple" 8
  (mkTTemplate [ mkTPattern "hallSubgroup" [vpVar "H", vpVar "G", vpVar "h"]
               , mkTPattern "simple" [vpVar "G"]
               ])
  applyHallNormal
  where
    applyHallNormal [Fact _ [hVal,gVal,_] _ _, Fact _ [g2Val] _ _]
      | gVal == g2Val = case (hVal,gVal) of
          (Sym h, Sym g) -> [TOFact (mkFactP PNormal [Sym h, Sym g])]
          _ -> []
    applyHallNormal _ = []

-- If numSylow(p,G,n) and we have divides(n,q) and divides(p,n-1) and only one divisor k of q satisfies k≡1 mod p, force numSylow(p,G,k)
sylowUniquenessFromDivCong :: Theorem
sylowUniquenessFromDivCong = mkTheoremT "SylowUniquenessFromDivCong" 15
  (mkTTemplate [ mkTPattern "numSylow" [vpVar "p", vpVar "G", vpVar "n"]
               , mkTPattern "divides" [vpVar "n", vpVar "q"]
               , mkTPattern "divides" [vpVar "p", vpVar "m"]
               ])
  applySylowUnique
  where
    applySylowUnique [Fact _ [pVal,gVal,nVal] _ _, Fact _ [n2Val,qVal] _ _, Fact _ [p2Val,mVal] _ _]
      | nVal == n2Val && pVal == p2Val =
          case (pVal,nVal,qVal,mVal,gVal) of
            (Nat p, Nat n, Nat q, Nat m, Sym g) ->
              if m == n - 1 && q > 0 then
                 let candidates = [d | d <- divisorsOf q, d `mod` p == 1]
                 in case candidates of
                      [k] | k /= n -> [TOFact (mkFactP PNumSylow [Nat p, Sym g, Nat k])]
                      _ -> []
              else []
            _ -> []
    applySylowUnique _ = []
    divisorsOf x = [d | d <- [1..x], x `mod` d == 0]

-- New parity theorem: simple_group_action (Python) analogue.
-- If G acts transitively on n points and is simple with n>1, embed into A_n via subgroup(G, A_n) and alternating_group(A_n,n).
-- This complements 'embedInAlternating' (which uses numSylow) covering the action route present in Python engine.
simpleGroupActionAlt :: Theorem
simpleGroupActionAlt = mkTheoremT "SimpleGroupAction" 12
  (mkTTemplate [ mkTPattern "transitiveAction" [vpVar "G", vpVar "n"]
               , mkTPattern "simple" [vpVar "G"]
               ])
  applySimpleGroupActionAlt
  where
    applySimpleGroupActionAlt [Fact _ [gVal,nVal] _ _, Fact _ [gVal2] _ _]
      | gVal == gVal2 = case (gVal,nVal) of
          (Sym g, Nat n) | n > 1 ->
             let aName = Sym ("A_" ++ show n)
             in [ TOFact (mkFactP PSubgroup [Sym g, aName])
                , TOFact (mkFactP PAlternatingGroup [aName, Nat n])
                ]
          _ -> []
    applySimpleGroupActionAlt _ = []

-- New parity theorem: normalizer_everything_implies_normal from Python.
-- If normalizer(G,H,X) and orders of G and X coincide, infer normal(H,G).
-- We omit the extra H order guard used in the refined equality theorem to ensure parity completeness.
normalizerEverythingImpliesNormal :: Theorem
normalizerEverythingImpliesNormal = mkTheoremT "NormalizerEverythingImpliesNormal" 7
  (mkTTemplate [ mkTPattern "normalizer" [vpVar "G", vpVar "H", vpVar "X"]
               , mkTPattern "order" [vpVar "G", vpVar "n"]
               , mkTPattern "order" [vpVar "X", vpVar "n"]
               ])
  applyNormalizerEverything
  where
    applyNormalizerEverything [Fact _ [gVal,hVal,xVal] _ _, Fact _ [g2Val,nVal] _ _, Fact _ [x2Val,n2Val] _ _]
      | gVal == g2Val && xVal == x2Val && nVal == n2Val =
          case (gVal,hVal) of
            (Sym g, Sym h) -> [TOFact (mkFactP PNormal [Sym h, Sym g])]
            _ -> []
    applyNormalizerEverything _ = []