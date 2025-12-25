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
import NumberTheory (maxPDivisor)
import Memoization (numSylowMemo, primeFactorsMemo)
import Predicates
import Theorems.Common (arg2, arg3, hyper, stdThm, withNum2)

ruleSylow :: [Fact] -> Maybe [Conclusion]
ruleSylow [factGroup, factOrder] =
  case (factArgs factGroup, arg2 factOrder) of
    ([gArg], Just (_gArg2, nArg)) ->
      case nArg of
        Num groupOrder -> Just $
          let groupName = argText gArg
              buildForP p =
                let pk = p ^ maxPDivisor groupOrder p
                    base = facts
                      [ sylowPOrder (sym groupName) (num p) (num pk)
                      , sylowPSubgroup (fresh (show p)) (num p) (sym groupName)
                      , order (fresh (show p)) (num pk)
                      ]
                    nps = numSylowMemo p groupOrder
                    disFacts =
                      [ numSylowFact (num p) (sym groupName) (num n)
                      | n <- nps
                      ]
                 in case disFacts of
                      [single] -> base ++ [CFact single]
                      _ -> base ++ [disj disFacts]
           in concatMap buildForP (primeFactorsMemo groupOrder)
        _ -> Nothing -- Not a Num arg
    _ -> Nothing
ruleSylow _ = Nothing

sylowTheorem :: Thm
sylowTheorem = hyper "sylow"
  [group (var "G"), order (var "G") (var "n")]
  ruleSylow

ruleSingleSylowNotSimple :: [Fact] -> Maybe [Conclusion]
ruleSingleSylowNotSimple [factSylow, _factNum, factOrder] =
  case (arg3 factSylow, arg2 factOrder) of
    (Just (_hArg, pArg, gArg), Just (_gArg2, nArg)) ->
      case (pArg, nArg) of
        (Num p, Num n0) ->
          let g = argText gArg
              pPower = isPowerOfP n0 p
           in if n0 == 0 || pPower then Nothing else Just [CFact (notSimple (sym g))]
        _ -> Nothing -- Not Num args
    _ -> Nothing
  where
    isPowerOfP n p'
      | n == 1 = True
      | n <= 0 = False
      | n `mod` p' /= 0 = False
      | otherwise = isPowerOfP (n `div` p') p'
ruleSingleSylowNotSimple _ = Nothing

singleSylowNotSimple :: Thm
singleSylowNotSimple = hyper "single_sylow_normal"
  [ sylowPSubgroup (var "H") (var "p") (var "G")
  , numSylowFact (var "p") (var "G") (exact "1")
  , order (var "G") (var "n")
  ]
  ruleSingleSylowNotSimple

simpleNotSimple :: Thm
simpleNotSimple = stdThm "not_simple"
  [simple (var "G"), notSimple (var "G")]
  [falseFact]

ruleEmbedInAn :: [Fact] -> Maybe [Conclusion]
ruleEmbedInAn [factNum, _factSimple] =
  case arg3 factNum of
    Just (_pArg, gArg, nPArg) ->
      case nPArg of
        Num nP ->
          let g = argText gArg
           in if nP > 1
                then Just
                  [ CFact (subgroup (sym g) (fresh "alt"))
                  , CFact (alternatingGroup (fresh "alt") (num nP))
                  ]
                else Nothing
        _ -> Nothing -- Not a Num arg
    _ -> Nothing
ruleEmbedInAn _ = Nothing

embedInAn :: Thm
embedInAn = hyper "embed_An"
  [numSylowFact (var "p") (var "G") (var "n_p"), simple (var "G")]
  ruleEmbedInAn


ruleAlternatingOrder :: [Fact] -> Maybe [Conclusion]
ruleAlternatingOrder [factAlt] = do
  (aArg, n) <- withNum2 factAlt (,)
  let a = argText aArg
      factorial' :: Integer -> Integer
      factorial' m = foldl' (*) 1 [1 .. m]
      orderVal
        | n == 1 = 1
        | otherwise = factorial' (fromIntegral n) `div` 2
  Just [CFact (order (sym a) (num (fromInteger orderVal)))]
ruleAlternatingOrder _ = Nothing

alternatingOrder :: Thm
alternatingOrder = hyper "alternating_order"
  [alternatingGroup (var "A") (var "n")]
  ruleAlternatingOrder

lagrange :: Thm
lagrange = stdThm "lagrange"
  [subgroup (var "H") (var "G"), order (var "H") (var "n"), order (var "G") (var "m")]
  [divides (var "n") (var "m")]

ruleDividesContradiction :: [Fact] -> Maybe [Conclusion]
ruleDividesContradiction [factDiv] =
  case factArgs factDiv of
    [Num m, Num n] | n `mod` m /= 0 -> Just [CFact falseFact]
    _ -> Nothing
ruleDividesContradiction _ = Nothing

dividesContradiction :: Thm
dividesContradiction = hyper "divides_contradiction"
  [divides (var "m") (var "n")]
  ruleDividesContradiction

ruleAlternatingSimple :: [Fact] -> Maybe [Conclusion]
ruleAlternatingSimple [factAlt] = do
  (aArg, n) <- withNum2 factAlt (,)
  if n >= 5 then Just [CFact (simple (sym (argText aArg)))] else Nothing
ruleAlternatingSimple _ = Nothing

alternatingSimple :: Thm
alternatingSimple = hyper "alternating_simple"
  [alternatingGroup (var "A") (var "n")]
  ruleAlternatingSimple

ruleSubgroupIndex :: [Fact] -> Maybe [Conclusion]
ruleSubgroupIndex [factSub, factH, factG] =
  case (arg2 factSub, arg2 factH, arg2 factG) of
    (Just (hArg, gArg), Just (_hArg2, mArg), Just (_gArg2, nArg)) ->
      case (mArg, nArg) of
        (Num m, Num n) ->
          let h = argText hArg
              g = argText gArg
           in if m /= 0 && n `mod` m == 0
                then Just [CFact (index (sym g) (sym h) (num (n `div` m)))]
                else Nothing
        _ -> Nothing -- Not Num args
    _ -> Nothing
ruleSubgroupIndex _ = Nothing

subgroupIndex :: Thm
subgroupIndex = hyper "subgroup_index"
  [subgroup (var "H") (var "G"), order (var "H") (var "m"), order (var "G") (var "n")]
  ruleSubgroupIndex

cosetAction :: Thm
cosetAction = stdThm "coset_action"
  [index (var "G") (var "H") (var "n")]
  [transitiveAction (var "G") (var "n")]

ruleSimpleGroupAction :: [Fact] -> Maybe [Conclusion]
ruleSimpleGroupAction [factAction, _factSimple] =
  case arg2 factAction of
    Just (gArg, nArg) ->
      case nArg of
        Num n ->
          let g = argText gArg
           in if n > 1
                then Just
                  [ CFact (subgroup (sym g) (fresh "alt"))
                  , CFact (alternatingGroup (fresh "alt") (num n))
                  ]
                else Nothing
        _ -> Nothing -- Not a Num arg
    _ -> Nothing
ruleSimpleGroupAction _ = Nothing

simpleGroupAction :: Thm
simpleGroupAction = hyper "simple_group_action"
  [transitiveAction (var "G") (var "n"), simple (var "G")]
  ruleSimpleGroupAction
