module Generators where

import Core
import Test.QuickCheck
import qualified Data.Set as Set

-- Generator for valid identifiers (alphanumeric strings)
genIdentifier :: Gen String
genIdentifier = do
  first <- elements (['a'..'z'] ++ ['A'..'Z'])
  rest <- listOf (elements (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9']))
  return (first : take 10 rest)  -- Limit length to 10

-- Generator for Arguments
instance Arbitrary Arg where
  arbitrary = oneof
    [ Sym <$> genIdentifier
    , Var <$> genIdentifier
    , Exact <$> genIdentifier
    , Fresh <$> genIdentifier
    , Num <$> choose (1, 1000)  -- Generate numbers from 1 to 1000
    ]

  shrink (Sym s) = [Sym s' | s' <- shrink s, not (null s')]
  shrink (Var v) = [Var v' | v' <- shrink v, not (null v')]
  shrink (Exact e) = [Exact e' | e' <- shrink e, not (null e')]
  shrink (Fresh f) = [Fresh f' | f' <- shrink f, not (null f')]
  shrink (Num n) = [Num n' | n' <- shrink n, n' > 0]  -- Keep numbers positive

-- Generator for Facts (with at least one argument)
instance Arbitrary Fact where
  arbitrary = do
    name <- genIdentifier
    numArgs <- choose (1, 5)  -- Facts have 1-5 arguments
    args <- vectorOf numArgs arbitrary
    return (Fact name args)

  shrink (Fact name args) =
    [ Fact name' args | name' <- shrink name, not (null name') ] ++
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
genSym = Sym <$> genIdentifier

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
  return (Fact name args)

-- Generate a pair of unifiable facts
genUnifiablePair :: Gen (Fact, Fact)
genUnifiablePair = do
  name <- genIdentifier
  numArgs <- choose (1, 3)

  -- Generate template fact with variables (no Exact for simplicity)
  templateArgs <- vectorOf numArgs genVar

  -- Generate concrete fact with symbols
  concreteArgs <- vectorOf numArgs genSym

  return (Fact name templateArgs, Fact name concreteArgs)

-- Generate a pair of non-unifiable facts
genNonUnifiablePair :: Gen (Fact, Fact)
genNonUnifiablePair = oneof
  [ do -- Different names
      name1 <- genIdentifier
      name2 <- genIdentifier `suchThat` (/= name1)
      numArgs <- choose (1, 3)
      args1 <- vectorOf numArgs arbitrary
      args2 <- vectorOf numArgs arbitrary
      return (Fact name1 args1, Fact name2 args2)

  , do -- Same name, different arity
      name <- genIdentifier
      numArgs1 <- choose (1, 3)
      numArgs2 <- choose (1, 3) `suchThat` (/= numArgs1)
      args1 <- vectorOf numArgs1 arbitrary
      args2 <- vectorOf numArgs2 arbitrary
      return (Fact name args1, Fact name args2)

  , do -- Same name and arity, but conflicting exact matches
      name <- genIdentifier
      sym1 <- genIdentifier
      sym2 <- genIdentifier `suchThat` (/= sym1)
      return (Fact name [Exact sym1], Fact name [Sym sym2])
  ]

-- Generate a consistent variable substitution pattern
genConsistentVarPattern :: Gen Fact
genConsistentVarPattern = do
  name <- genIdentifier
  var <- genIdentifier
  numOccurrences <- choose (2, 4)
  let args = replicate numOccurrences (Var var)
  return (Fact name args)

-- Generate an inconsistent variable substitution pattern
genInconsistentVarPattern :: Gen (Fact, Fact)
genInconsistentVarPattern = do
  name <- genIdentifier
  var <- genIdentifier
  sym1 <- genIdentifier
  sym2 <- genIdentifier `suchThat` (/= sym1)

  let template = Fact name [Var var, Var var]
      concrete = Fact name [Sym sym1, Sym sym2]

  return (template, concrete)
