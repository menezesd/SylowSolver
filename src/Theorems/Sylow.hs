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
import NumberTheory (maxPDivisor)
import Memoization (numSylowMemo, primeFactorsMemo)
import Predicates
import Theorems.Common (arg2, arg3, asNum, hyper, stdThm, withArg2Num, withNum2)

ruleSylow :: [Fact] -> Maybe [Conclusion]
ruleSylow [factGroup, factOrder] =
  case (factArgs factGroup, arg2 factOrder) of
    ([gArg], Just (_gArg2, nArg)) ->
      case nArg of
        Num groupOrder -> Just $
          let groupName = argText gArg
              go = fromInteger groupOrder  -- convert to Int for number theory
              buildForP p =
                let pk = p ^ maxPDivisor go p
                    base = facts
                      [ sylowPOrder (sym groupName) (num p) (num pk)
                      , sylowPSubgroup (fresh (show p)) (num p) (sym groupName)
                      , order (fresh (show p)) (num pk)
                      ]
                    nps = numSylowMemo p go
                    disFacts =
                      [ numSylowFact (num p) (sym groupName) (num n)
                      | n <- nps
                      ]
                 in case disFacts of
                      [single] -> base ++ [CFact single]
                      _ -> base ++ [disj disFacts]
           in concatMap buildForP (primeFactorsMemo go)
        _ -> Nothing -- Not a Num arg
    _ -> Nothing
ruleSylow _ = Nothing

sylowTheorem :: Thm
sylowTheorem = hyper "sylow"
  [group (var "G"), order (var "G") (var "n")]
  ruleSylow

ruleSingleSylowNotSimple :: [Fact] -> Maybe [Conclusion]
ruleSingleSylowNotSimple [factSylow, _factNum, factOrder] =
  do
    (_hArg, pArg, gArg) <- arg3 factSylow
    p <- asNum pArg
    n0 <- withArg2Num factOrder (\_ n -> n)
    let g = argText gArg
    -- Skip only prime-order groups (which are simple).
    -- p-groups of order p^k (k>=2) are not simple (non-trivial center).
    if n0 <= 1 || n0 == p then Nothing else Just [CFact (notSimple (sym g))]
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
    Just (_pArg, gArg, Num nP) ->
      let g = argText gArg
       in if nP > 1
            then Just
              [ CFact (subgroup (sym g) (fresh "alt"))
              , CFact (alternatingGroup (fresh "alt") (num nP))
              ]
            else Nothing
    _ -> Nothing
ruleEmbedInAn _ = Nothing

embedInAn :: Thm
embedInAn = hyper "embed_An"
  [numSylowFact (var "p") (var "G") (var "n_p"), simple (var "G")]
  ruleEmbedInAn


ruleAlternatingOrder :: [Fact] -> Maybe [Conclusion]
ruleAlternatingOrder [factAlt] = do
  (aArg, n) <- withNum2 factAlt (,)
  -- Skip very large n to avoid computing huge factorials
  if n > 100 then Nothing else do
    let a = argText aArg
        orderVal :: Integer
        orderVal
          | n == 1 = 1
          | otherwise = product [1 .. n] `div` 2
    Just [CFact (order (sym a) (Num orderVal))]
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
  -- Skip very large n (we can't meaningfully reason about them)
  if n >= 5 && n <= 100 then Just [CFact (simple (sym (argText aArg)))] else Nothing
ruleAlternatingSimple _ = Nothing

alternatingSimple :: Thm
alternatingSimple = hyper "alternating_simple"
  [alternatingGroup (var "A") (var "n")]
  ruleAlternatingSimple

ruleSubgroupIndex :: [Fact] -> Maybe [Conclusion]
ruleSubgroupIndex [factSub, factH, factG] =
  case (arg2 factSub, withArg2Num factH (,), withArg2Num factG (,)) of
    (Just (hArg, gArg), Just (_, m), Just (_, n)) ->
      let h = argText hArg
          g = argText gArg
       in if m /= 0 && n `mod` m == 0
            then Just [CFact (index (sym g) (sym h) (num (n `div` m)))]
            else Nothing
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
    Just (gArg, Num n) ->
      let g = argText gArg
       in if n > 1
            then Just
              [ CFact (subgroup (sym g) (fresh "alt"))
              , CFact (alternatingGroup (fresh "alt") (num n))
              ]
            else Nothing
    _ -> Nothing
ruleSimpleGroupAction _ = Nothing

simpleGroupAction :: Thm
simpleGroupAction = hyper "simple_group_action"
  [transitiveAction (var "G") (var "n"), simple (var "G")]
  ruleSimpleGroupAction
