module Main where

import Auto (matchFactsToTheorem)
import Core
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Env
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests =
  testGroup
    "sylow-solver"
    [ testProperty "Exact args must match literally" propExactMatch
    , testProperty "Var args unify consistently" propVarUnify
    , testProperty "Fresh args behave like variables in matching" propFreshMatch
    , testCase "Disjunction coverage detects goal proven" caseDisjunctionCoverage
    , testCase "Disjunction coverage detects missing branch" caseDisjunctionMissing
    ]

propExactMatch :: String -> String -> Bool
propExactMatch g h =
  let template = [Fact "num_sylow" [exact "2", var "G"]]
      fMatch = Fact "num_sylow" [sym "2", sym g]
      fNoMatch = Fact "num_sylow" [sym "3", sym h]
      facts = [mkFactEntry 0 fMatch, mkFactEntry 1 fNoMatch]
      matches = matchFactsToTheorem template facts facts
   in length matches == 1 && feFact (head (head matches)) == fMatch

propVarUnify :: String -> String -> Bool
propVarUnify a b =
  let template = [Fact "foo" [var "X", var "X"]]
      f1 = Fact "foo" [sym a, sym b]
      facts = [mkFactEntry 0 f1]
      matches = matchFactsToTheorem template facts facts
   in if a == b
        then length matches == 1
        else null matches

propFreshMatch :: String -> Bool
propFreshMatch a =
  let template = [Fact "bar" [fresh "T"]]
      f1 = Fact "bar" [sym a]
      facts = [mkFactEntry 0 f1]
      matches = matchFactsToTheorem template facts facts
   in length matches == 1

caseDisjunctionCoverage :: Assertion
caseDisjunctionCoverage = do
  let goal = Fact "goal" []
      env0 = initEnv [] [] Map.empty goal
      disj = Disjunction [Fact "p" [], Fact "q" []]
      (env1, _) = addNewFacts env0 [NewConclusion (CDisj disj) [] Set.empty Nothing]
      dLabel = case peDisjunctions env1 of
        (d : _) -> deLabel d
        [] -> DisjId 0
      combos =
        [ Set.fromList [(dLabel, 0)]
        , Set.fromList [(dLabel, 1)]
        ]
      env2 = updateGoalAchieved env1 {peGoalDisCombos = combos}
  peGoalAchieved env2 @?= True

caseDisjunctionMissing :: Assertion
caseDisjunctionMissing = do
  let goal = Fact "goal" []
      env0 = initEnv [] [] Map.empty goal
      disj = Disjunction [Fact "p" [], Fact "q" []]
      (env1, _) = addNewFacts env0 [NewConclusion (CDisj disj) [] Set.empty Nothing]
      dLabel = case peDisjunctions env1 of
        (d : _) -> deLabel d
        [] -> DisjId 0
      combos =
        [ Set.fromList [(dLabel, 0)]
        ]
      env2 = updateGoalAchieved env1 {peGoalDisCombos = combos}
  peGoalAchieved env2 @?= False

mkFactEntry :: Int -> Fact -> FactEntry
mkFactEntry n fact =
  FactEntry
    { feFact = fact
    , feLabel = FactId n
    , feDependencies = []
    , feDisAncestors = Set.empty
    , feConcThm = Nothing
    , feUseful = False
    , feDepth = 0
    }
