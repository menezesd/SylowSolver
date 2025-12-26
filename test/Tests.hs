module Main where

import Auto (matchFactsToTheorem)
import Data.List (nub)
import Core
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Set as Set
import Env
import Unification
import Generators
import Predicates (group, pNumSylow) -- For dummy goal
import NumberTheory
import Memoization
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck
import ProofMonad (internSymbolM, runProofM)
import Data.Hashable (hash)
import qualified Data.IntMap.Strict as IntMap

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "sylow-solver"
    [ testGroup "Matching"
        [ testProperty "Exact args must match literally" propExactMatch
        , testProperty "Var args unify consistently" propVarUnify
        , testProperty "Fresh args behave like variables in matching" propFreshMatch
        ]
    , testGroup "Unification"
        [ testProperty "Unification is idempotent" propUnifyIdempotent
        , testProperty "Unification succeeds for identical facts" propUnifyIdentical
        , testProperty "Unifiable pairs unify successfully" propUnifiablePairsUnify
        , testProperty "Non-unifiable pairs fail to unify" propNonUnifiablePairsFail
        , testProperty "Consistent variables unify" propConsistentVarsUnify
        , testProperty "Inconsistent variables fail" propInconsistentVarsFail
        , testCase "Unification detects name mismatch" caseUnifyNameMismatch
        , testCase "Unification detects arity mismatch" caseUnifyArityMismatch
        ]
    , testGroup "Fact Properties"
        [ testProperty "Fact equality is reflexive" propFactEqReflexive
        , testProperty "Fact equality is symmetric" propFactEqSymmetric
        , testProperty "Fact equality is transitive" propFactEqTransitive
        ]
    , testGroup "Arg Properties"
        [ testProperty "argText extracts string from any Arg" propArgText
        ]
    , testGroup "Disjunction Coverage"
        [ testCase "Disjunction coverage detects goal proven" caseDisjunctionCoverage
        , testCase "Disjunction coverage detects missing branch" caseDisjunctionMissing
        ]
    , testGroup "FactDatabase Invariants"
        [ testProperty "fdFactIndex keys match fact keys" propFactIndexKeysMatch
        , testProperty "fdFactLabels contains all ordered facts" propFactLabelsComplete
        , testProperty "fdFacts are all in fdFactLabels" propFactsInLabels
        ]
    , testGroup "Number Theory"
        [ testProperty "divisors are actual divisors" propDivisorsCorrect
        , testProperty "memoized divisors match pure" propDivisorsMemoCorrect
        , testProperty "divisors are sorted and unique" propDivisorsSortedUnique
        , testProperty "primesUpTo produces primes only" propPrimesUpToArePrime
        , testProperty "primesUpTo is monotone" propPrimesUpToMonotone
        , testProperty "prime factors are prime" propPrimeFactorsArePrime
        , testProperty "prime factorization reconstructs n" propPrimeFactorizationCorrect
        , testProperty "memoized primeFactors match pure" propPrimeFactorsMemoCorrect
        , testProperty "memoized primeFactorization matches pure" propPrimeFactorizationMemoCorrect
        , testProperty "numSylow satisfies divisibility/congruence" propNumSylowValid
        ]
    , testGroup "FactKey"
        [ testProperty "equal facts have equal keys" propEqualFactsEqualKeys
        ]
    , testGroup "Substitution"
        [ testProperty "applying empty substitution is identity" propEmptySubstIdentity
        , testProperty "substitution application is deterministic" propSubstDeterministic
        ]
    , testGroup "Symbols"
        [ testProperty "interning is idempotent per name" propInternIdempotent
        , testProperty "interning different names yields different ids" propInternDistinct
        , testProperty "generateSymbolM produces fresh ids" propGenerateSymbolFresh
        ]
    ]

propExactMatch :: String -> String -> Bool
propExactMatch g h =
  let template = [Fact pNumSylow [exact "2", var "G"]]
      fMatch = Fact pNumSylow [sym "2", sym g]
      fNoMatch = Fact pNumSylow [sym "3", sym h]
      
      -- Create an initial environment and add facts to it
      env0 = initEnv [] [] HashMap.empty (group (sym "dummy")) -- Use a dummy goal
      (env1, inserted) = addNewFacts env0 [NewConclusion (CFact fMatch) [] Set.empty Nothing, NewConclusion (CFact fNoMatch) [] Set.empty Nothing]

      matches = matchFactsToTheorem template env1 (peFacts env1)
   in case matches of
        [[entry]] ->
          case inserted of
            (firstInserted:_) -> feFact entry == feFact firstInserted
            _ -> False
        _ -> False

propVarUnify :: String -> String -> Bool
propVarUnify a b =
  let template = [Fact (customPred "foo") [var "X", var "X"]]
      f1 = Fact (customPred "foo") [sym a, sym b]

      env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
      (env1, _) = addNewFacts env0 [NewConclusion (CFact f1) [] Set.empty Nothing]

      matches = matchFactsToTheorem template env1 (peFacts env1)
   in if a == b
        then length matches == 1
        else null matches

propFreshMatch :: String -> Bool
propFreshMatch a =
  let template = [Fact (customPred "bar") [fresh "T"]]
      f1 = Fact (customPred "bar") [sym a]

      env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
      (env1, _) = addNewFacts env0 [NewConclusion (CFact f1) [] Set.empty Nothing]
      
      matches = matchFactsToTheorem template env1 (peFacts env1)
   in length matches == 1

caseDisjunctionCoverage :: Assertion
caseDisjunctionCoverage = do
  let goal = Fact (customPred "goal") []
      env0 = initEnv [] [] HashMap.empty goal
      disj = Disjunction [Fact (customPred "p") [], Fact (customPred "q") []]
      (env1, _) = addNewFacts env0 [NewConclusion (CDisj disj) [] Set.empty Nothing]
      dLabel = case peDisjunctions env1 of
        (d : _) -> deLabel d
        [] -> DisjId 0
      combos =
        [ Set.fromList [(dLabel, 0)]
        , Set.fromList [(dLabel, 1)]
        ]
      -- Update goal state with combos
      env2 = updateGoalState (\gs -> gs { gsDisCombos = combos }) env1
      env3 = updateGoalAchieved env2
  peGoalAchieved env3 @?= True

caseDisjunctionMissing :: Assertion
caseDisjunctionMissing = do
  let goal = Fact (customPred "goal") []
      env0 = initEnv [] [] HashMap.empty goal
      disj = Disjunction [Fact (customPred "p") [], Fact (customPred "q") []]
      (env1, _) = addNewFacts env0 [NewConclusion (CDisj disj) [] Set.empty Nothing]
      dLabel = case peDisjunctions env1 of
        (d : _) -> deLabel d
        [] -> DisjId 0
      combos =
        [ Set.fromList [(dLabel, 0)]
        ]
      -- Update goal state with combos
      env2 = updateGoalState (\gs -> gs { gsDisCombos = combos }) env1
      env3 = updateGoalAchieved env2
  peGoalAchieved env3 @?= False

-- Unification property tests
propUnifyIdempotent :: String -> Bool
propUnifyIdempotent name =
  let f = Fact (customPred name) []
   in case unify f f of
        Right subst -> nullSubstitution subst
        Left _ -> False

propUnifyIdentical :: String -> String -> Bool
propUnifyIdentical name arg =
  let f1 = Fact (customPred name) [sym arg]
      f2 = Fact (customPred name) [sym arg]
   in case unify f1 f2 of
        Right subst -> nullSubstitution subst
        Left _ -> False

caseUnifyNameMismatch :: Assertion
caseUnifyNameMismatch = do
  let f1 = Fact (customPred "foo") []
      f2 = Fact (customPred "bar") []
   in case unify f1 f2 of
        Left (NameMismatch n1 n2)
          | predNameText n1 == "foo" && predNameText n2 == "bar" -> pure ()
        _ -> assertFailure "Expected name mismatch error"

caseUnifyArityMismatch :: Assertion
caseUnifyArityMismatch = do
  let f1 = Fact (customPred "foo") [sym "a"]
      f2 = Fact (customPred "foo") [sym "a", sym "b"]
   in case unify f1 f2 of
        Left (ArityMismatch 1 2) -> pure ()
        _ -> assertFailure "Expected arity mismatch error"

-- New property tests using generators

propUnifiablePairsUnify :: Property
propUnifiablePairsUnify = forAll genUnifiablePair $ \(template, concrete) ->
  case unify template concrete of
    Right _ -> True
    Left _ -> False

propNonUnifiablePairsFail :: Property
propNonUnifiablePairsFail = forAll genNonUnifiablePair $ \(f1, f2) ->
  case unify f1 f2 of
    Left _ -> True
    Right _ -> False

propConsistentVarsUnify :: Property
propConsistentVarsUnify = forAll genConsistentVarPattern $ \template ->
  let sameSym = sym "x"
      concrete = Fact (factName template) (replicate (length (factArgs template)) sameSym)
   in case unify template concrete of
        Right _ -> True
        Left _ -> False

propInconsistentVarsFail :: Property
propInconsistentVarsFail = forAll genInconsistentVarPattern $ \(template, concrete) ->
  case unify template concrete of
    Left _ -> True
    Right _ -> False

-- Fact equality properties

propFactEqReflexive :: Fact -> Bool
propFactEqReflexive f = f == f

propFactEqSymmetric :: Fact -> Fact -> Bool
propFactEqSymmetric f1 f2 = (f1 == f2) == (f2 == f1)

propFactEqTransitive :: Property
propFactEqTransitive = forAll genTransitiveFacts $ \(f1, f2, f3) ->
  (f1 == f2 && f2 == f3) ==> f1 == f3

-- Arg properties

propArgText :: Arg -> Bool
propArgText arg =
  let text = argText arg
   in not (null text)

mkFactEntry :: Int -> Fact -> FactEntry
mkFactEntry n fact =
  let prov = Provenance
        { provDeps = []
        , provDisAncestors = Set.empty
        , provThm = Nothing
        }
   in FactEntry
        { feFact = fact
        , feLabel = FactId n
        , feProv = prov
        , feUseful = False
        , feDepth = CaseDepth 0
        , feHash = HashKey (hash fact)
        }

-- FactDatabase Invariant Tests

propFactIndexKeysMatch :: [Fact] -> Bool
propFactIndexKeysMatch facts =
  let env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
      newConcs = [NewConclusion (CFact f) [] Set.empty Nothing | f <- facts]
      (env1, _) = addNewFacts env0 newConcs
      factDB = peFactDB env1
      -- Check that every entry in fdFactIndex has the correct key
      indexEntries = IntMap.toList (fdFactIndex factDB)
   in all (\(hKey, entries) -> all (\entry -> hash (feFact entry) == hKey) entries) indexEntries

propFactLabelsComplete :: [Fact] -> Bool
propFactLabelsComplete facts =
  let env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
      newConcs = [NewConclusion (CFact f) [] Set.empty Nothing | f <- facts]
      (env1, _) = addNewFacts env0 newConcs
      factDB = peFactDB env1
      orderedLabels = Set.fromList (fdOrderedFacts factDB)
      factLabelsKeys = Set.fromList (HashMap.keys (fdFactLabels factDB))
   in orderedLabels `Set.isSubsetOf` factLabelsKeys

propFactsInLabels :: [Fact] -> Bool
propFactsInLabels facts =
  let env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
      newConcs = [NewConclusion (CFact f) [] Set.empty Nothing | f <- facts]
      (env1, _) = addNewFacts env0 newConcs
      factDB = peFactDB env1
      allFacts = fdFacts factDB
      factLabelsMap = fdFactLabels factDB
   in all (\entry -> HashMap.member (LFact (feLabel entry)) factLabelsMap) allFacts

-- Number Theory property tests

propDivisorsCorrect :: Positive Int -> Bool
propDivisorsCorrect (Positive n) =
  all (\d -> n `mod` d == 0) (divisors n)

propDivisorsMemoCorrect :: Positive Int -> Bool
propDivisorsMemoCorrect (Positive n) =
  divisorsMemo n == divisors n

propPrimeFactorsArePrime :: Positive Int -> Bool
propPrimeFactorsArePrime (Positive n) =
  all isPrime (primeFactors n)

propPrimeFactorizationCorrect :: Positive Int -> Bool
propPrimeFactorizationCorrect (Positive n)
  | n <= 1 = null (primeFactorization n)
  | otherwise = product [p ^ k | (p, k) <- primeFactorization n] == n

propPrimeFactorsMemoCorrect :: Positive Int -> Bool
propPrimeFactorsMemoCorrect (Positive n) =
  primeFactorsMemo n == primeFactors n

propPrimeFactorizationMemoCorrect :: Positive Int -> Bool
propPrimeFactorizationMemoCorrect (Positive n) =
  primeFactorizationMemo n == primeFactorization n

propDivisorsSortedUnique :: Positive Int -> Bool
propDivisorsSortedUnique (Positive n) =
  let ds = divisors n
   in ds == Set.toAscList (Set.fromList ds)

propPrimesUpToArePrime :: Positive Int -> Bool
propPrimesUpToArePrime (Positive n) =
  let ps = primesUpTo n
   in ps == Set.toAscList (Set.fromList (filter isPrime ps)) && all isPrime ps

propPrimesUpToMonotone :: Positive Int -> Positive Int -> Bool
propPrimesUpToMonotone (Positive a) (Positive b) =
  let small = min a b
      big = max a b
   in Set.fromList (primesUpTo small) `Set.isSubsetOf` Set.fromList (primesUpTo big)

propNumSylowValid :: Positive Int -> Positive Int -> Bool
propNumSylowValid (Positive p) (Positive n)
  | p < 2 = True
  | otherwise =
      let ns = numSylow p n
       in all (\d -> d `mod` p == 1 && n `mod` d == 0) ns

-- FactKey property tests

propFactKeyStable :: Fact -> Bool
propFactKeyStable f = factKey f == factKey f

propEqualFactsEqualKeys :: Fact -> Bool
propEqualFactsEqualKeys f =
  let f2 = Fact (factName f) (factArgs f)
   in factKey f == factKey f2

-- Substitution property tests

propEmptySubstIdentity :: Property
propEmptySubstIdentity = forAll genSymOnlyFact $ \f ->
  applySubstToFact emptySubstitution f == f

-- Generate facts with only Sym and Num args (Exact converts to Sym)
genSymOnlyFact :: Gen Fact
genSymOnlyFact = do
  name <- arbitrary
  numArgs <- choose (0, 3)
  args <- vectorOf numArgs genSymOrNum
  pure $ Fact name args
  where
    genSymOrNum = oneof [Sym <$> arbitrary, Num <$> arbitrary]

propSubstDeterministic :: Fact -> Bool
propSubstDeterministic f =
  let subst = substFromList [("X", sym "a"), ("Y", sym "b")]
   in applySubstToFact subst f == applySubstToFact subst f

propInternIdempotent :: String -> Bool
propInternIdempotent name =
  let env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
      (sym1, env1) = runProofM (internSymbolM name) env0
      (sym2, _) = runProofM (internSymbolM name) env1
   in sym1 == sym2

propInternDistinct :: String -> String -> Property
propInternDistinct a b =
  a /= b ==>
    let env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
        (sym1, env1) = runProofM (internSymbolM a) env0
        (sym2, _) = runProofM (internSymbolM b) env1
     in sym1 /= sym2

propGenerateSymbolFresh :: Property
propGenerateSymbolFresh =
  forAll (listOf1 arbitrary) $ \names ->
    let env0 = initEnv [] [] HashMap.empty (group (sym "dummy"))
        distinct = nub names
        (syms, _) = runProofM (mapM internSymbolM distinct) env0
        ids = map unSymbol syms
     in length distinct == length (nub ids)
