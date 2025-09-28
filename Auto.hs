-- | Auto.hs
--
-- Lightweight theorem-proving engine for the Sylow solver.
-- This module contains fact matching and proof search functionality.
--
-- This is a Haskell port of the Python auto2.py module.

{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

module Auto
  ( -- * Fact generation helpers
    group
  , order
  , sylowPOrder
  , sylowPSubgroup
  , alternatingGroup
  , numSylow
  , simple
  , notSimple
  , subgroup
  , divides
  , false
  , index
  , transitiveAction
  , orderPkLowerBound
  , moreThanOneSylow
  , intersection
  , normalizer
  , orderLowerBound
  , maxSylowIntersection
  , properSubgroup
  , normal
  , normalizerOfSylowIntersection
  , subgroupIndex
  , groupEmbeds
  , alternatingGroup
  , orFact
  
  -- * Pattern matching and theorem application
  , MatchDict
  , matchFactsToTemplate
  , matchFactsToTheorem
  
  -- * Built-in theorems
  , sylowTheorem
  , singleSylowNotSimple
  , pGroupNotSimple
  , simpleNotSimple
  , embedInAn
  , alternatingOrder
  , lagrange
  , dividesContradiction
  , alternatingSimple
  , countOrderPkElements
  , countingContradiction
  , checkPPower
  , isPrimePowerGE2
  , multipleSylows
  , possibleMaxIntersections
  , intersectionOfSylows
  , normalizerSylowIntersection
  , normalizerEverythingImpliesNormal
  , normalSubgroupToNotSimple
  , ruleOutMaxIntersections
  , ruleOutNormalizerOfIntersectionOrder
  , embeddingContradiction
  , cosetActionTheorem
  , simpleGroupActionTheorem
  , enhancedSubgroupIndex
  , multipleCountingContradiction
  ) where

import Core
import qualified NumberTheory as NT
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (catMaybes)
import Control.Monad (foldM)
import Text.Read (readMaybe)

-- | Type alias for variable matching dictionary
type MatchDict = Map String String

-- * Fact generation helpers

-- | G is a group
group :: String -> Fact
group g = createFact "group" [g]

-- | The order of G is n
order :: String -> String -> Fact
order g n = createFact "order" [g, n]

-- | The order of a sylow p-subgroup of G is pk
sylowPOrder :: String -> String -> String -> Fact
sylowPOrder g p pk = createFact "sylow_order" [g, p, pk]

-- | P is a sylow p-subgroup of G
sylowPSubgroup :: String -> String -> String -> Fact
sylowPSubgroup p_sub p g = createFact "sylow_p_subgroup" [p_sub, p, g]

-- | A is the alternating group on n letters
alternatingGroup :: String -> String -> Fact
alternatingGroup a n = createFact "alternating_group" [a, n]

-- | The number of sylow p-subgroups of G is n
numSylow :: String -> String -> String -> Fact
numSylow p g n = createFact "num_sylow" [p, g, n]

-- | G is simple
simple :: String -> Fact
simple g = createFact "simple" [g]

-- | G is not simple
notSimple :: String -> Fact
notSimple g = createFact "not_simple" [g]

-- | H is a subgroup of G
subgroup :: String -> String -> Fact
subgroup h g = createFact "subgroup" [h, g]

-- | m divides n
divides :: String -> String -> Fact
divides m n = createFact "divides" [m, n]

-- | A false statement
false :: Fact
false = createFact "false" []

-- | H's index in G is n
index :: String -> String -> String -> Fact
index g h n = createFact "index" [g, h, n]

-- | G acts transitively on a set of size n
transitiveAction :: String -> String -> Fact
transitiveAction g n = createFact "transitive_action" [g, n]

-- | Number of elements of order p^k for some k>0 is at least N
orderPkLowerBound :: String -> String -> String -> Fact
orderPkLowerBound g p n = createFact "order_pk_lower_bound" [g, p, n]

-- | G has more than one sylow p subgroup
moreThanOneSylow :: String -> String -> Fact
moreThanOneSylow p g = createFact "more_than_one_sylow" [p, g]

-- | The intersection of A and B is C
intersection :: String -> String -> String -> Fact
intersection a b c = createFact "intersection" [a, b, c]

-- | N_G(H) = K
normalizer :: String -> String -> String -> Fact
normalizer g h k = createFact "normalizer" [g, h, k]

-- | The order of H is at least n
orderLowerBound :: String -> String -> Fact
orderLowerBound h n = createFact "order_lower_bound" [h, n]

-- | The maximum intersection of two distinct sylow p-subgroups of G is m
maxSylowIntersection :: String -> String -> String -> Fact
maxSylowIntersection g p m = createFact "max_sylow_intersection" [g, p, m]

-- | H is a proper subgroup of G
properSubgroup :: String -> String -> Fact
properSubgroup h g = createFact "proper_subgroup" [h, g]

-- | H is a normal subgroup of G
normal :: String -> String -> Fact
normal h g = createFact "normal" [h, g]

-- | T is the normalizer of intersection for two sylow-p subgroups of G
normalizerOfSylowIntersection :: String -> String -> String -> Fact
normalizerOfSylowIntersection p g t = createFact "normalizer_of_sylow_intersection" [p, g, t]

-- | Subgroup index: subgroupIndex(H, G, n) means H has index n in G
subgroupIndex :: String -> String -> String -> Fact
subgroupIndex h g n = createFact "subgroup_index" [h, g, n]

-- | Group embeds: groupEmbeds(G, H) means G can be embedded in H
groupEmbeds :: String -> String -> Fact
groupEmbeds g h = createFact "group_embeds" [g, h]





-- | Create a disjunction (OR) of two facts
orFact :: Fact -> Fact -> Disjunction
orFact f1 f2 = createDisjunction [f1, f2]

-- * Pattern matching functions

-- | Find all facts that match a given template structure.
-- Returns matching facts and their associated variable bindings.
matchFactsToTemplate :: Fact -> [Fact] -> MatchDict -> ([Fact], [MatchDict])
matchFactsToTemplate template facts initMatchDict =
  let templateName = factName template
      templateArgs = factArgs template
      
      matchesAndDicts = catMaybes [tryMatch templateName templateArgs initMatchDict fact | fact <- facts]
  in unzip matchesAndDicts
  where
    tryMatch templateName templateArgs initDict fact
      | factName fact /= templateName = Nothing
      | length (factArgs fact) /= length templateArgs = Nothing
      | otherwise = 
          case foldM matchArg initDict (zip templateArgs (factArgs fact)) of
            Just matchDict -> Just (fact, matchDict)
            Nothing -> Nothing
    
    matchArg dict (tempArg, factArg)
      | take 1 tempArg == "*" = -- Exact match required
          if drop 1 tempArg == factArg 
          then Just dict 
          else Nothing
      | Map.member tempArg dict = -- Variable already bound
          if dict Map.! tempArg == factArg 
          then Just dict 
          else Nothing
      | otherwise = -- Bind new variable
          Just (Map.insert tempArg factArg dict)

-- | Given a list of facts and theorem input structure, find all possible matching combinations.
matchFactsToTheorem :: [Fact] -> [Fact] -> Maybe [Fact] -> [[Fact]]
matchFactsToTheorem thmFacts facts newFacts =
  let factsToSearch = maybe facts id newFacts
      initialMatches = [[]]
      initialDicts = [Map.empty]
      initialUsesNew = [False]
  in go thmFacts initialMatches initialDicts initialUsesNew factsToSearch
  where
    go [] matches _ usesNewList _ = 
      [match | (match, usesNew) <- zip matches usesNewList, usesNew]
    go (thmFact:restThmFacts) curMatches curDicts usesNewList searchFacts =
      let newMatchesAndData = concatMap (extendMatch thmFact searchFacts) 
                                       (zip3 curMatches curDicts usesNewList)
          (newMatches, newDicts, newUsesNewList) = unzip3 newMatchesAndData
      in go restThmFacts newMatches newDicts newUsesNewList searchFacts
    
    extendMatch thmFact searchFacts (curMatch, curDict, usesNew) =
      let (matchingFacts, matchingDicts) = matchFactsToTemplate thmFact searchFacts curDict
          combinations = zip matchingFacts matchingDicts
          isNewFact newFact = maybe True (newFact `elem`) newFacts  -- If newFacts is Nothing, treat all as new
      in [(curMatch ++ [newFact], newDict, usesNew || isNewFact newFact)
         | (newFact, newDict) <- combinations]

-- * Built-in theorems

-- | Sylow's theorem - generates sylow subgroups for each prime factor
sylowTheorem :: HyperTheorem
sylowTheorem = createHyperTheorem inputFacts ruleSylow "sylow"
  where
    inputFacts = [group "G", order "G" "n"]
    
    ruleSylow facts = 
      case facts of
        (gFact:oFact:_) ->
          let groupNameArgs = factArgs gFact
              orderArgs = factArgs oFact
          in case (groupNameArgs, orderArgs) of
               ([groupName], [_g, nStr]) ->
                 case readMaybe nStr :: Maybe Int of
                   Nothing -> []
                   Just groupOrder ->
                     let primeFactors' = NT.primeFactors groupOrder
                     in concatMap (generateSylowFacts groupName groupOrder) primeFactors'
               _ -> []
        _ -> []
    
    generateSylowFacts groupName groupOrder p =
      let sylowOrder = p ^ NT.maxPDivisor groupOrder p
          sylowVar = "?" ++ show p
          sylowOrderStr = show sylowOrder
          pStr = show p
          nPList = NT.numSylow p groupOrder
          baseFacts = [ CF (sylowPOrder groupName pStr sylowOrderStr)
                      , CF (sylowPSubgroup sylowVar pStr groupName)
                      , CF (order sylowVar sylowOrderStr)
                      ]
          numSylowConcs = case nPList of
            [k] -> [CF (numSylow pStr groupName (show k))]
            ks | not (null ks) ->
                  [ CD (createDisjunction [ numSylow pStr groupName (show k) | k <- ks ]) ]
               | otherwise -> []
      in baseFacts ++ numSylowConcs

-- | Check if n is a power of p
checkPPower :: Int -> Int -> Bool
checkPPower n p
  | n == 1 = True
  | n `mod` p /= 0 = False
  | otherwise = checkPPower (n `div` p) p

-- | Single sylow subgroup implies not simple (unless group is p-group)
singleSylowNotSimple :: HyperTheorem
singleSylowNotSimple = createHyperTheorem inputFacts ruleSingleSylow "single_sylow_normal"
  where
    inputFacts = [ sylowPSubgroup "H" "p" "G"
                 , numSylow "p" "G" "*1"
                 , order "G" "n"
                 ]

    ruleSingleSylow facts =
      case facts of
        (spFact:_numFact:ordFact:_) ->
          case factArgs spFact of
            [_h, pStr, g] ->
              case factArgs ordFact of
                [_g2, nStr] ->
                  case (readMaybe pStr :: Maybe Int, readMaybe nStr :: Maybe Int) of
                    (Just p, Just n) ->
                      let isPPower = checkPPower n p
                      in if isPPower then [] else [CF (notSimple g)]
                    _ -> []
                _ -> []
            _ -> []
        _ -> []
    
-- | Check if n is a prime power p^k with k >= 2
isPrimePowerGE2 :: Int -> Bool
isPrimePowerGE2 n = case NT.primeFactorization n of
  [(_, e)] | e >= 2 -> True
  _ -> False

-- | P-groups of order p^k with k >= 2 are not simple
-- | P-groups of order p^k with k >= 2 are not simple
pGroupNotSimple :: HyperTheorem
pGroupNotSimple = createHyperTheorem inputFacts rulePGroup "p_group_not_simple"
  where
    inputFacts = [order "G" "n"]

    rulePGroup facts =
      case facts of
        (ordFact:_) ->
          case factArgs ordFact of
            [g, nStr] ->
              case readMaybe nStr :: Maybe Int of
                Just n -> if isPrimePowerGE2 n && g == "G" then [CF (notSimple g)] else []
                _ -> []
            _ -> []
        _ -> []

-- | Simple + not_simple = false
simpleNotSimple :: Theorem
simpleNotSimple = createTheorem inputFacts outputFacts "not_simple"
  where
    inputFacts = [simple "G", notSimple "G"]
    outputFacts = [false]

-- | Embed group into alternating group based on sylow subgroup count
embedInAn :: HyperTheorem
embedInAn = createHyperTheorem inputFacts ruleEmbed "embed_An"
  where
    inputFacts = [numSylow "p" "G" "n_p", simple "G"]

    ruleEmbed facts =
      case facts of
        (nsFact:_simp:_) ->
          case factArgs nsFact of
            [_p, g, nStr] ->
              case readMaybe nStr :: Maybe Int of
                Just nP | nP > 1 -> [ CF (subgroup g "?alt"), CF (alternatingGroup "?alt" (show nP)) ]
                _ -> []
            _ -> []
        _ -> []

-- | Alternating group order calculation
alternatingOrder :: HyperTheorem
alternatingOrder = createHyperTheorem inputFacts ruleOrder "alternating_order"
  where
    inputFacts = [alternatingGroup "A" "n"]

    ruleOrder facts =
      case facts of
        (aFact:_) ->
          case factArgs aFact of
            [a, nStr] ->
              case readMaybe nStr :: Maybe Int of
                Nothing -> []
                Just n -> if n <= 0 || n > 1000 
                         then []
                         else let orderVal = if n == 1 then 1 else factorial n `div` 2
                              in [CF (order a (show orderVal))]
            _ -> []
        _ -> []

    factorial n = product [1..n]

-- | Lagrange's theorem - subgroup order divides group order
lagrange :: Theorem
lagrange = createTheorem inputFacts outputFacts "lagrange"
  where
    inputFacts = [ subgroup "H" "G"
                 , order "H" "n"
                 , order "G" "m"
                 ]
    outputFacts = [divides "n" "m"]

-- | Check divisibility and generate contradiction if false
dividesContradiction :: HyperTheorem
dividesContradiction = createHyperTheorem inputFacts ruleCheck "divides_contradiction"
  where
    inputFacts = [divides "m" "n"]

    ruleCheck facts =
      case facts of
        (dFact:_) ->
          case factArgs dFact of
            [mStr, nStr] ->
              case (readMaybe mStr :: Maybe Int, readMaybe nStr :: Maybe Int) of
                (Just m, Just n) -> if n `mod` m /= 0 then [CF false] else []
                _ -> []
            _ -> []
        _ -> []

-- | Alternating groups A_n with n >= 5 are simple
alternatingSimple :: HyperTheorem
alternatingSimple = createHyperTheorem inputFacts ruleSimple "alternating_simple"
  where
    inputFacts = [alternatingGroup "A" "n"]

    ruleSimple facts =
      case facts of
        (aFact:_) ->
          case factArgs aFact of
            [a, nStr] ->
              case readMaybe nStr :: Maybe Int of
                Just n | n >= 5 -> [CF (simple a)]
                _ -> []
            _ -> []
        _ -> []

-- | Count elements of order p^k in a group
countOrderPkElements :: HyperTheorem
countOrderPkElements = createHyperTheorem inputFacts ruleCount "count_order_pk_elements"
  where
    inputFacts = [ sylowPSubgroup "P" "p" "G"
                 , numSylow "p" "G" "n_p"
                 , order "P" "pk"
                 ]

    ruleCount facts =
      case facts of
        (spFact:nFact:ordFact:_) ->
          case factArgs spFact of
            [_pVar, pStr, g] ->
              case factArgs nFact of
                [_p2, _g2, nPStr] ->
                  case factArgs ordFact of
                    [_p3, pkStr] ->
                      case (readMaybe pStr :: Maybe Int, readMaybe nPStr :: Maybe Int, readMaybe pkStr :: Maybe Int) of
                        (Just p, Just nP, Just pk) ->
                          let lowerBound = if pk == p
                                           then (p - 1) * nP  -- Cyclic of prime order
                                           else if nP == 1
                                                then pk - 1   -- Unique subgroup
                                                else pk       -- Multiple subgroups
                          in [CF (orderPkLowerBound g (show p) (show lowerBound))]
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | Detect contradictions by counting elements
countingContradiction :: HyperTheorem
countingContradiction = createHyperTheorem inputFacts ruleContradiction "counting_contradiction"
  where
    inputFacts = [ orderPkLowerBound "G" "p1" "N1"
                 , orderPkLowerBound "G" "p2" "N2" 
                 , order "G" "n"
                 ]

    ruleContradiction facts =
      case facts of
        (b1:b2:ordG:_) ->
          case factArgs b1 of
            [_g1, p1Str, n1Str] ->
              case factArgs b2 of
                [_g2, p2Str, n2Str] ->
                  case factArgs ordG of
                    [_g3, nStr] ->
                      case ( readMaybe p1Str :: Maybe Int
                           , readMaybe p2Str :: Maybe Int
                           , readMaybe n1Str :: Maybe Int
                           , readMaybe n2Str :: Maybe Int
                           , readMaybe nStr  :: Maybe Int) of
                        (Just p1, Just p2, Just n1, Just n2, Just n) ->
                          if p1 /= p2 && n1 + n2 + 1 > n then [CF false] else []
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | More than one Sylow p-subgroup when the count n_p > 1
multipleSylows :: HyperTheorem
multipleSylows = createHyperTheorem inputFacts rule "multiple_sylows"
  where
    inputFacts = [numSylow "p" "G" "n_p"]

    rule facts =
      case facts of
        (ns:_) ->
          case factArgs ns of
            [pStr, g, nStr] ->
              case readMaybe nStr :: Maybe Int of
                Just nP | nP > 1 -> [CF (moreThanOneSylow pStr g)]
                _ -> []
            _ -> []
        _ -> []

-- | Possible maximal intersections of distinct Sylow p-subgroups
possibleMaxIntersections :: HyperTheorem
possibleMaxIntersections = createHyperTheorem inputFacts rule "possible_max_intersections"
  where
    inputFacts = [moreThanOneSylow "p" "G", sylowPOrder "G" "p" "pk"]

    rule facts =
      case facts of
        (mFact:soFact:_) ->
          case factArgs mFact of
            [pStr, g] ->
              case factArgs soFact of
                [_g2, _p2, pkStr] ->
                  case (readMaybe pStr :: Maybe Int, readMaybe pkStr :: Maybe Int) of
                    (Just p, Just pk) ->
                      let intersections = takeWhile (< pk) $ iterate (* p) 1
                          alts = [ maxSylowIntersection g pStr (show pl) | pl <- intersections ]
                      in if null alts then [] else if length alts == 1 then [CF (head alts)] else [CD (createDisjunction alts)]
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | From a maximal intersection size, produce intersecting Sylow subgroups
intersectionOfSylows :: HyperTheorem
intersectionOfSylows = createHyperTheorem inputFacts rule "intersection_of_sylows"
  where
    inputFacts = [maxSylowIntersection "G" "p" "pl"]
    rule facts =
      case facts of
        (mi:_) ->
          case factArgs mi of
            [g, pStr, plStr] ->
              [ CF (sylowPSubgroup "?P" pStr g)
              , CF (sylowPSubgroup "?Q" pStr g)
              , CF (intersection "?P" "?Q" "?R")
              , CF (order "?R" plStr)
              ]
            _ -> []
        _ -> []

-- | Normalizer of a Sylow intersection and possible sizes of the normalizer
normalizerSylowIntersection :: HyperTheorem
normalizerSylowIntersection = createHyperTheorem inputFacts rule "normalizer_sylow_intersection"
  where
    inputFacts = [ sylowPSubgroup "P" "p" "G"
                 , sylowPSubgroup "Q" "p" "G"
                 , intersection "P" "Q" "R"
                 , order "R" "pl"
                 , sylowPOrder "G" "p" "pk"
                 , order "G" "n"
                 ]

    rule facts =
      case facts of
        (sp1:_sp2:_int:ordR:so:ordG:_) ->
          case factArgs sp1 of
            [_pSub1, pStr, g] ->
              case factArgs ordR of
                [_r, plStr] ->
                  case factArgs so of
                    [_g2, _p2, pkStr] ->
                      case factArgs ordG of
                        [_g3, nStr] ->
                          case ( readMaybe pStr :: Maybe Int
                               , readMaybe plStr :: Maybe Int
                               , readMaybe pkStr :: Maybe Int
                               , readMaybe nStr  :: Maybe Int) of
                            (Just p, Just pl, Just pk, Just n) | pk == pl * p ->
                              let t = "?T"
                                  base = [ CF (normalizer g "?R" t)
                                         , CF (subgroup t g)
                                         , CF (normalizerOfSylowIntersection pStr g t)
                                         ]
                                  poss = [ d | d <- NT.divisors n, d > pk, d `mod` pk == 0 ]
                              in case poss of
                                   []  -> base
                                   [d] -> base ++ [CF (order t (show d))]
                                   _   -> base ++ [CD (createDisjunction [order t (show d) | d <- poss])]
                            _ -> []
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | If the normalizer equals G in order, the subgroup is normal
normalizerEverythingImpliesNormal :: HyperTheorem
normalizerEverythingImpliesNormal = createHyperTheorem inputFacts rule "normalizer_everything_implies_normal"
  where
    inputFacts = [normalizer "G" "H" "X", order "G" "n", order "X" "n"]

    rule facts =
      case facts of
        (nrm:_og:_ox:_) ->
          case factArgs nrm of
            [gName, hName, _xName] -> [CF (normal hName gName)]
            _ -> []
        _ -> []

-- | A nontrivial proper normal subgroup implies not simple
normalSubgroupToNotSimple :: HyperTheorem
normalSubgroupToNotSimple = createHyperTheorem inputFacts rule "normal_subgroup_to_not_simple"
  where
    inputFacts = [normal "H" "G", order "H" "h", order "G" "g"]

    rule facts =
      case facts of
        (nrm:ordH:ordG:_) ->
          case factArgs nrm of
            [_hName, gName] ->
              case factArgs ordH of
                [_h2, hStr] ->
                  case factArgs ordG of
                    [_g2, gStr] ->
                      case (readMaybe hStr :: Maybe Int, readMaybe gStr :: Maybe Int) of
                        (Just h, Just g) | 1 < h && h < g -> [CF (notSimple gName)]
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | Rule out impossible maximal intersections via congruence condition
ruleOutMaxIntersections :: HyperTheorem
ruleOutMaxIntersections = createHyperTheorem inputFacts rule "rule_out_max_intersections"
  where
    inputFacts = [ numSylow "p" "G" "np"
                 , maxSylowIntersection "G" "p" "pl"
                 , sylowPOrder "G" "p" "pk"
                 ]

    rule facts =
      case facts of
        (ns:mi:so:_) ->
          case factArgs ns of
            [_p1, _g1, npStr] ->
              case factArgs mi of
                [_g2, _p2, plStr] ->
                  case factArgs so of
                    [_g3, _p3, pkStr] ->
                      case (readMaybe npStr :: Maybe Int, readMaybe plStr :: Maybe Int, readMaybe pkStr :: Maybe Int) of
                        (Just np, Just pl, Just pk) ->
                          if pk `mod` pl /= 0 then [] else if np `mod` (pk `div` pl) /= 1 then [CF false] else []
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | Rule out orders of the normalizer that would force a unique Sylow in T
ruleOutNormalizerOfIntersectionOrder :: HyperTheorem
ruleOutNormalizerOfIntersectionOrder = createHyperTheorem inputFacts rule "rule_out_normalizer_of_intersection_order"
  where
    inputFacts = [normalizerOfSylowIntersection "p" "G" "T", order "T" "k"]

    rule facts =
      case facts of
        (noi:ordT:_) ->
          case factArgs noi of
            [pStr, _g, _t] ->
              case factArgs ordT of
                [_t2, kStr] ->
                  case (readMaybe pStr :: Maybe Int, readMaybe kStr :: Maybe Int) of
                    (Just p, Just k) -> let nps = NT.numSylow p k in if length nps == 1 then [CF false] else []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []
-- | If G embeds in A_n but |G| doesn't divide |A_n|, we have a contradiction  
embeddingContradiction :: HyperTheorem
embeddingContradiction = createHyperTheorem inputFacts rule "embedding_contradiction"
  where
    inputFacts = [groupEmbeds "G" "An", order "G" "n"]

    rule facts =
      case facts of
        (embed:ordG:_) ->
          case factArgs embed of
            [_gName, anStr] ->
              case factArgs ordG of
                [_g2, nStr] ->
                  case readMaybe nStr :: Maybe Int of
                    Just n -> 
                      -- Extract alternating group order from A_k format
                      let anOrder = case anStr of
                            'A':'_':kStr -> case readMaybe kStr of
                              Just k | k >= 2 -> Just $ product [1..k] `div` 2
                              _ -> Nothing
                            _ -> Nothing
                      in case anOrder of
                           Just an | n > an -> [CF false] -- G is too big to embed
                           _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | Coset action theorem: if H has index n in G, then G acts transitively on n elements  
cosetActionTheorem :: HyperTheorem
cosetActionTheorem = createHyperTheorem inputFacts rule "coset_action"
  where
    inputFacts = [index "G" "H" "n"]
    
    rule facts =
      case facts of
        (idx:_) ->
          case factArgs idx of
            [gName, _hName, nStr] -> [CF (transitiveAction gName nStr)]
            _ -> []
        _ -> []

-- | Simple group action theorem: if G is simple and acts transitively on n elements, then G embeds in A_n
simpleGroupActionTheorem :: HyperTheorem  
simpleGroupActionTheorem = createHyperTheorem inputFacts rule "simple_group_action"
  where
    inputFacts = [transitiveAction "G" "n", simple "G"]
    
    rule facts =
      case facts of
        (ta:simp:_) ->
          case (factArgs ta, factArgs simp) of  
            ([gName, nStr], [g2]) | gName == g2 -> 
              [CF (subgroup gName ("A" ++ nStr)), CF (alternatingGroup ("A" ++ nStr) nStr)]
            _ -> []
        _ -> []

-- | Enhanced subgroup index calculation with better logic
enhancedSubgroupIndex :: HyperTheorem
enhancedSubgroupIndex = createHyperTheorem inputFacts rule "enhanced_subgroup_index"
  where
    inputFacts = [subgroup "H" "G", order "H" "m", order "G" "n"]

    rule facts =
      case facts of
        (sub:ordH:ordG:_) ->
          case factArgs sub of
            [hName, gName] ->
              case factArgs ordH of
                [_h2, mStr] ->
                  case factArgs ordG of
                    [_g2, nStr] ->
                      case (readMaybe mStr :: Maybe Int, readMaybe nStr :: Maybe Int) of
                        (Just m, Just n) | n `mod` m == 0 ->
                          let idx = n `div` m
                          in [ CF (index gName hName (show idx))
                             , CF (transitiveAction gName (show idx))
                             ]
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | Enhanced counting contradiction for multiple primes
multipleCountingContradiction :: HyperTheorem
multipleCountingContradiction = createHyperTheorem inputFacts rule "multiple_counting_contradiction"
  where
    inputFacts = [ orderLowerBound "G" "N1"
                 , orderLowerBound "G" "N2"
                 , order "G" "n"
                 ]

    rule facts =
      case facts of
        (olb1:olb2:ordG:_) ->
          case factArgs olb1 of
            [_g1, n1Str] ->
              case factArgs olb2 of
                [_g2, n2Str] ->
                  case factArgs ordG of
                    [_g3, nStr] ->
                      case ( readMaybe n1Str :: Maybe Int
                           , readMaybe n2Str :: Maybe Int
                           , readMaybe nStr :: Maybe Int) of
                        (Just n1, Just n2, Just n)
                          | n1 + n2 + 1 > n -> [CF false]
                          | otherwise -> []
                        _ -> []
                    _ -> []
                _ -> []
            _ -> []
        _ -> []

-- | Transitive action theorem: if H has index n in G, then G acts transitively on n elements\ntransitiveActionTheorem :: HyperTheorem\ntransitiveActionTheorem = createHyperTheorem inputFacts rule \"transitive_action_theorem\"\n  where\n    inputFacts = [index \"G\" \"H\" \"n\"]\n    \n    rule facts =\n      case facts of\n        (idx:_) ->\n          case factArgs idx of\n            [gName, _hName, nStr] -> [CF (transitiveAction gName nStr)]\n            _ -> []\n        _ -> []\n\n-- | Enhanced subgroup index calculation with better logic\nenhancedSubgroupIndex :: HyperTheorem\nenhancedSubgroupIndex = createHyperTheorem inputFacts rule \"enhanced_subgroup_index\"\n  where\n    inputFacts = [subgroup \"H\" \"G\", order \"H\" \"m\", order \"G\" \"n\"]\n\n    rule facts =\n      case facts of\n        (sub:ordH:ordG:_) ->\n          case factArgs sub of\n            [hName, gName] ->\n              case factArgs ordH of\n                [_h2, mStr] ->\n                  case factArgs ordG of\n                    [_g2, nStr] ->\n                      case (readMaybe mStr :: Maybe Int, readMaybe nStr :: Maybe Int) of\n                        (Just m, Just n) | n `mod` m == 0 ->\n                          let idx = n `div` m\n                          in [ CF (index gName hName (show idx))\n                             , CF (transitiveAction gName (show idx))\n                             ]\n                        _ -> []\n                    _ -> []\n                _ -> []\n            _ -> []\n        _ -> []\n\n-- | Enhanced counting contradiction for multiple primes\nmultipleCountingContradiction :: HyperTheorem\nmultipleCountingContradiction = createHyperTheorem inputFacts rule \"multiple_counting_contradiction\"\n  where\n    inputFacts = [ orderLowerBound \"G\" \"p1\" \"N1\"\n                 , orderLowerBound \"G\" \"p2\" \"N2\"\n                 , order \"G\" \"n\"\n                 ]\n\n    rule facts =\n      case facts of\n        (olb1:olb2:ordG:_) ->\n          case factArgs olb1 of\n            [_g1, p1Str, n1Str] ->\n              case factArgs olb2 of\n                [_g2, p2Str, n2Str] ->\n                  case factArgs ordG of\n                    [_g3, nStr] ->\n                      case ( readMaybe p1Str :: Maybe Int\n                           , readMaybe p2Str :: Maybe Int\n                           , readMaybe n1Str :: Maybe Int\n                           , readMaybe n2Str :: Maybe Int\n                           , readMaybe nStr :: Maybe Int) of\n                        (Just p1, Just p2, Just n1, Just n2, Just n)\n                          | p1 /= p2 && n1 + n2 + 1 > n -> [CF false]\n                          | otherwise -> []\n                        _ -> []\n                    _ -> []\n                _ -> []\n            _ -> []\n        _ -> []
