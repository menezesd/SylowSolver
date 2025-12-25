{-# OPTIONS_GHC -Wno-orphans #-}

module Generators where

import Core
import Data.Hashable (hash)
import Test.QuickCheck

-- Generator for valid identifiers (alphanumeric strings)
genIdentifier :: Gen String
genIdentifier = do
  first <- elements (['a'..'z'] ++ ['A'..'Z'])
  rest <- listOf (elements (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']))
  return (first : take 10 rest)  -- Limit length to 10

instance Arbitrary PredName where
  arbitrary =
    oneof
      [ pure PGroup
      , pure POrder
      , pure PSylowOrder
      , pure PSylowPSubgroup
      , pure PAlternatingGroup
      , pure PNumSylow
      , pure PSimple
      , pure PNotSimple
      , pure PSubgroup
      , pure PDivides
      , pure PFalse
      , pure PIndex
      , pure PTransitiveAction
      , pure POrderPkLowerBound
      , pure PMoreThanOneSylow
      , pure PIntersection
      , pure PNormalizer
      , pure POrderLowerBound
      , pure PMaxSylowIntersection
      , pure PProperSubgroup
      , pure PNormal
      , pure PNormalizerOfSylowIntersection
      , PCustom <$> genIdentifier
      ]

  shrink (PCustom s) = [PCustom s' | s' <- shrink s, not (null s')]
  shrink _ = []

symbolFromName :: String -> Symbol
symbolFromName name = Symbol (abs (hash name)) name

instance Arbitrary Symbol where
  arbitrary = symbolFromName <$> genIdentifier
  shrink (Symbol _ name) = [symbolFromName name' | name' <- shrink name, not (null name')]

-- Generator for Arguments
instance Arbitrary Arg where
  arbitrary = oneof
    [ Sym <$> arbitrary
    , Var <$> genIdentifier
    , Exact <$> genIdentifier
    , Fresh <$> genIdentifier
    , Num <$> choose (1, 1000)  -- Generate numbers from 1 to 1000
    ]

  shrink (Sym s) = Sym <$> shrink s
  shrink (Var v) = [Var v' | v' <- shrink v, not (null v')]
  shrink (Exact e) = [Exact e' | e' <- shrink e, not (null e')]
  shrink (Fresh f) = [Fresh f' | f' <- shrink f, not (null f')]
  shrink (Num n) = [Num n' | n' <- shrink n, n' > 0]  -- Keep numbers positive

-- Generator for Facts (with at least one argument)
instance Arbitrary Fact where
  arbitrary = do
    name <- genIdentifier
    numArgs <- choose (0, 5)  -- Facts have 0-5 arguments
    args <- vectorOf numArgs arbitrary
    return (Fact (customPred name) args)

  shrink (Fact name args) =
    [ Fact (customPred name') args | name' <- shrink (predNameText name), not (null name') ] ++
    [ Fact name args' | args' <- shrink args, not (null args') ]

-- Generator for Disjunctions
instance Arbitrary Disjunction where
  arbitrary = do
    numFacts <- choose (2, 4)  -- 2-4 facts in a disjunction
    facts <- vectorOf numFacts arbitrary
    return (Disjunction facts)

  shrink (Disjunction facts) =
    [ Disjunction facts' | facts' <- shrink facts, length facts' >= 2 ]

-- Generator for specific argument types

-- Generate a symbol argument
genSym :: Gen Arg
genSym = sym <$> genIdentifier

-- Generate a variable argument
genVar :: Gen Arg
genVar = Var <$> genIdentifier

-- Generate an exact argument
genExact :: Gen Arg
genExact = Exact <$> genIdentifier

-- Generate a fresh argument
genFresh :: Gen Arg
genFresh = Fresh <$> genIdentifier

-- Generate a fact with specific argument types
genFactWithPattern :: [Gen Arg] -> String -> Gen Fact
genFactWithPattern argGens name = do
  args <- sequence argGens
  return (Fact (customPred name) args)

-- Generate a pair of unifiable facts
genUnifiablePair :: Gen (Fact, Fact)
genUnifiablePair = do
  name <- genIdentifier
  numArgs <- choose (1, 3)

  -- Generate template fact with variables (no Exact for simplicity)
  templateArgs <- vectorOf numArgs genVar

  -- Ensure repeated variables map to the same symbol so unification succeeds
  let vars = [v | Var v <- templateArgs]
  symMapping <- mapM (\v -> do symId <- genIdentifier; pure (v, symbolFromName symId)) vars
  let lookupSym v = maybe (symbolFromName v) id (lookup v symMapping)
      concreteArgs = [Sym (lookupSym v) | Var v <- templateArgs]

  return (Fact (customPred name) templateArgs, Fact (customPred name) concreteArgs)

-- Generate a pair of non-unifiable facts
genNonUnifiablePair :: Gen (Fact, Fact)
genNonUnifiablePair = oneof
  [ do -- Different names
      name1 <- genIdentifier
      name2 <- genIdentifier `suchThat` (/= name1)
      numArgs <- choose (1, 3)
      args1 <- vectorOf numArgs arbitrary
      args2 <- vectorOf numArgs arbitrary
      return (Fact (customPred name1) args1, Fact (customPred name2) args2)

  , do -- Same name, different arity
      name <- genIdentifier
      numArgs1 <- choose (1, 3)
      numArgs2 <- choose (1, 3) `suchThat` (/= numArgs1)
      args1 <- vectorOf numArgs1 arbitrary
      args2 <- vectorOf numArgs2 arbitrary
      return (Fact (customPred name) args1, Fact (customPred name) args2)

  , do -- Same name and arity, but conflicting exact matches
      name <- genIdentifier
      sym1 <- genIdentifier
      sym2 <- genIdentifier `suchThat` (/= sym1)
      return (Fact (customPred name) [Exact sym1], Fact (customPred name) [Sym (symbolFromName sym2)])
  ]

-- Generate a consistent variable substitution pattern
genConsistentVarPattern :: Gen Fact
genConsistentVarPattern = do
  name <- genIdentifier
  varName <- genIdentifier
  numOccurrences <- choose (2, 4)
  let args = replicate numOccurrences (Var varName)
  return (Fact (customPred name) args)

-- Generate an inconsistent variable substitution pattern
genInconsistentVarPattern :: Gen (Fact, Fact)
genInconsistentVarPattern = do
  name <- genIdentifier
  varName <- genIdentifier
  sym1 <- genIdentifier
  sym2 <- genIdentifier `suchThat` (/= sym1)

  let template = Fact (customPred name) [Var varName, Var varName]
      concrete = Fact (customPred name) [Sym (symbolFromName sym1), Sym (symbolFromName sym2)]

  return (template, concrete)

-- Generator for facts designed to frequently satisfy transitivity conditions
genTransitiveFacts :: Gen (Fact, Fact, Fact)
genTransitiveFacts = do
  f_base <- arbitrary

  -- f1 is either f_base or an arbitrary fact
  f1 <- frequency
    [ (7, pure f_base)
    , (3, arbitrary)
    ]

  -- f2 is either f1 or an arbitrary fact
  f2 <- frequency
    [ (7, pure f1)
    , (3, arbitrary)
    ]

  -- f3 is either f2 or an arbitrary fact
  f3 <- frequency
    [ (7, pure f2)
    , (3, arbitrary)
    ]

  pure (f1, f2, f3)
