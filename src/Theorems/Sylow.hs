module Theorems.Sylow
  ( sylowTheorem
  , singleSylowNotSimple
  , simpleNotSimple
  , embedInAn
  , alternatingOrder
  , lagrange
  , dividesContradiction
  , alternatingSimple
  , subgroupIndex
  , cosetAction
  , simpleGroupAction
  ) where

import Core
import Data.List (foldl')
import NumberTheory
import Predicates
import Theorems.Common

ruleSylow :: [Fact] -> [Conclusion]
ruleSylow [factGroup, factOrder] =
  case (factArgs factGroup, arg2 factOrder) of
    ([gArg], Just (_gArg2, nArg)) ->
      let groupName = argText gArg
          groupOrder = readInt (argText nArg)
          buildForP p =
            let pk = p ^ maxPDivisor groupOrder p
                base =
                  [ CFact (sylowPOrder (sym groupName) (sym (show p)) (sym (show pk)))
                  , CFact (sylowPSubgroup (fresh (show p)) (sym (show p)) (sym groupName))
                  , CFact (order (fresh (show p)) (sym (show pk)))
                  ]
                nps = numSylow p groupOrder
                disFacts =
                  [ numSylowFact (sym (show p)) (sym groupName) (sym (show n))
                  | n <- nps
                  ]
             in if length disFacts == 1
                  then base ++ map CFact disFacts
                  else base ++ [CDisj (Disjunction disFacts)]
       in concatMap buildForP (primeFactors groupOrder)
    _ -> []
ruleSylow _ = []

sylowTheorem :: Thm
sylowTheorem =
  Hyper
    ( HyperTheorem
        "sylow"
        [group (var "G"), order (var "G") (var "n")]
        ruleSylow
    )

ruleSingleSylowNotSimple :: [Fact] -> [Conclusion]
ruleSingleSylowNotSimple [factSylow, _factNum, factOrder] =
  case (arg3 factSylow, arg2 factOrder) of
    (Just (_hArg, pArg, gArg), Just (_gArg2, nArg)) ->
      let g = argText gArg
          p = readInt (argText pArg)
          n0 = readInt (argText nArg)
          pPower = isPowerOfP n0 p
       in if n0 == 0 || pPower then [] else [CFact (notSimple (sym g))]
    _ -> []
  where
    isPowerOfP n p'
      | n == 1 = True
      | n <= 0 = False
      | n `mod` p' /= 0 = False
      | otherwise = isPowerOfP (n `div` p') p'
ruleSingleSylowNotSimple _ = []

singleSylowNotSimple :: Thm
singleSylowNotSimple =
  Hyper
    ( HyperTheorem
        "single_sylow_normal"
        [ sylowPSubgroup (var "H") (var "p") (var "G")
        , numSylowFact (var "p") (var "G") (exact "1")
        , order (var "G") (var "n")
        ]
        ruleSingleSylowNotSimple
    )

simpleNotSimple :: Thm
simpleNotSimple =
  Std
    (Theorem "not_simple" [simple (var "G"), notSimple (var "G")] [falseFact])

ruleEmbedInAn :: [Fact] -> [Conclusion]
ruleEmbedInAn [factNum, _factSimple] =
  case arg3 factNum of
    Just (_pArg, gArg, nPArg) ->
      let nP = readInt (argText nPArg)
          g = argText gArg
       in if nP > 1
            then
              [ CFact (subgroup (sym g) (fresh "alt"))
              , CFact (alternatingGroup (fresh "alt") (sym (show nP)))
              ]
            else []
    _ -> []
ruleEmbedInAn _ = []

embedInAn :: Thm
embedInAn =
  Hyper
    ( HyperTheorem
        "embed_An"
        [numSylowFact (var "p") (var "G") (var "n_p"), simple (var "G")]
        ruleEmbedInAn
    )

ruleAlternatingOrder :: [Fact] -> [Conclusion]
ruleAlternatingOrder [factAlt] =
  case arg2 factAlt of
    Just (aArg, nArg) ->
      let a = argText aArg
          n = readInt (argText nArg)
          factorial m = foldl' (*) 1 [1 .. fromIntegral m]
          orderVal
            | n > 1000 = 0
            | n == 1 = 1
            | otherwise = fromIntegral (factorial n `div` 2)
       in if n > 1000 then [] else [CFact (order (sym a) (sym (show orderVal)))]
    _ -> []
ruleAlternatingOrder _ = []

alternatingOrder :: Thm
alternatingOrder =
  Hyper
    ( HyperTheorem
        "alternating_order"
        [alternatingGroup (var "A") (var "n")]
        ruleAlternatingOrder
    )

lagrange :: Thm
lagrange =
  Std
    ( Theorem
        "lagrange"
        [subgroup (var "H") (var "G"), order (var "H") (var "n"), order (var "G") (var "m")]
        [divides (var "n") (var "m")]
    )

ruleDividesContradiction :: [Fact] -> [Conclusion]
ruleDividesContradiction [factDiv] =
  case arg2 factDiv of
    Just (mArg, nArg) ->
      let m = readInt (argText mArg)
          n = readInt (argText nArg)
       in if n `mod` m /= 0 then [CFact falseFact] else []
    _ -> []
ruleDividesContradiction _ = []

dividesContradiction :: Thm
dividesContradiction =
  Hyper
    ( HyperTheorem
        "divides_contradiction"
        [divides (var "m") (var "n")]
        ruleDividesContradiction
    )

ruleAlternatingSimple :: [Fact] -> [Conclusion]
ruleAlternatingSimple [factAlt] =
  case arg2 factAlt of
    Just (aArg, nArg) ->
      let n = readInt (argText nArg)
          a = argText aArg
       in if n >= 5 then [CFact (simple (sym a))] else []
    _ -> []
ruleAlternatingSimple _ = []

alternatingSimple :: Thm
alternatingSimple =
  Hyper
    ( HyperTheorem
        "alternating_simple"
        [alternatingGroup (var "A") (var "n")]
        ruleAlternatingSimple
    )

ruleSubgroupIndex :: [Fact] -> [Conclusion]
ruleSubgroupIndex [factSub, factH, factG] =
  case (arg2 factSub, arg2 factH, arg2 factG) of
    (Just (hArg, gArg), Just (_hArg2, mArg), Just (_gArg2, nArg)) ->
      let m = readInt (argText mArg)
          n = readInt (argText nArg)
          h = argText hArg
          g = argText gArg
       in if m /= 0 && n `mod` m == 0
            then [CFact (index (sym g) (sym h) (sym (show (n `div` m))))]
            else []
    _ -> []
ruleSubgroupIndex _ = []

subgroupIndex :: Thm
subgroupIndex =
  Hyper
    ( HyperTheorem
        "subgroup_index"
        [subgroup (var "H") (var "G"), order (var "H") (var "m"), order (var "G") (var "n")]
        ruleSubgroupIndex
    )

cosetAction :: Thm
cosetAction =
  Std
    (Theorem "coset_action" [index (var "G") (var "H") (var "n")] [transitiveAction (var "G") (var "n")])

ruleSimpleGroupAction :: [Fact] -> [Conclusion]
ruleSimpleGroupAction [factAction, _factSimple] =
  case arg2 factAction of
    Just (gArg, nArg) ->
      let n = readInt (argText nArg)
          g = argText gArg
       in if n > 1
            then
              [ CFact (subgroup (sym g) (fresh "alt"))
              , CFact (alternatingGroup (fresh "alt") (sym (show n)))
              ]
            else []
    _ -> []
ruleSimpleGroupAction _ = []

simpleGroupAction :: Thm
simpleGroupAction =
  Hyper
    ( HyperTheorem
        "simple_group_action"
        [transitiveAction (var "G") (var "n"), simple (var "G")]
        ruleSimpleGroupAction
    )
