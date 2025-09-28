-- | AutoSpec.hs
--
-- Tests for the Auto module theorem proving functionality.

module AutoSpec where

import Test.Hspec
import Auto
import Core
import Environment
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

spec :: Spec
spec = do
  describe "Fact generators" $ do
    it "creates group facts correctly" $ do
      let groupFact = group "G"
      factName groupFact `shouldBe` "group"
      factArgs groupFact `shouldBe` ["G"]
      
    it "creates order facts correctly" $ do
      let orderFact = order "G" "12"
      factName orderFact `shouldBe` "order"
      factArgs orderFact `shouldBe` ["G", "12"]
      
    it "creates various mathematical facts" $ do
      let simpleFact = simple "G"
          notSimpleFact = notSimple "G"
          subgroupFact = subgroup "H" "G"
          dividesFact = divides "6" "12"
      
      factName simpleFact `shouldBe` "simple"
      factName notSimpleFact `shouldBe` "not_simple"  
      factName subgroupFact `shouldBe` "subgroup"
      factName dividesFact `shouldBe` "divides"
      
  describe "Pattern matching" $ do
    it "matches facts to templates with variables" $ do
      let template = createFact "group" ["G"]
          facts = [group "TestGroup", order "TestGroup" "6", group "AnotherGroup"]
          initDict = Map.empty
          (matches, dicts) = matchFactsToTemplate template facts initDict
      
      length matches `shouldBe` 2  -- Two group facts should match
      length dicts `shouldBe` 2
      
    it "handles exact matches with asterisk syntax" $ do
      let template = createFact "num_sylow" ["p", "G", "*1"]  -- Exact match for "1"
          facts = [ numSylow "2" "G" "1"
                  , numSylow "2" "G" "3"  
                  , numSylow "3" "G" "1"
                  ]
          (matches, _) = matchFactsToTemplate template facts Map.empty
      
      length matches `shouldBe` 2  -- Only facts with "1" should match
      
    it "maintains variable consistency" $ do
      let template = createFact "order" ["G", "n"]
          facts = [order "TestGroup" "12", order "TestGroup" "6"]
          initDict = Map.singleton "G" "TestGroup"  -- G must be TestGroup
          (matches, _) = matchFactsToTemplate template facts initDict
      
      length matches `shouldBe` 2  -- Both should match since G is consistent
      
  describe "Built-in theorems" $ do
    it "Lagrange theorem has correct structure" $ do
      let thm = lagrange
      theoremName thm `shouldBe` "lagrange"
      length (theoremInputFacts thm) `shouldBe` 3  -- subgroup, order H, order G
      length (theoremConclusions thm) `shouldBe` 1  -- divides
      
    it "Simple + not_simple = false theorem" $ do
      let thm = simpleNotSimple
      theoremName thm `shouldBe` "not_simple"
      length (theoremInputFacts thm) `shouldBe` 2
      length (theoremConclusions thm) `shouldBe` 1
      factName (head (theoremConclusions thm)) `shouldBe` "false"
      
  describe "HyperTheorem rules" $ do
    it "Alternating order computes correctly for small n" $ do
      let hyperThm = alternatingOrder
          inputFact = alternatingGroup "A5" "5"
          result = hyperTheoremRule hyperThm [inputFact]
          
      length result `shouldBe` 1
      case head result of
        CF orderFact -> do
          factName orderFact `shouldBe` "order"
          factArgs orderFact `shouldBe` ["A5", "60"]  -- 5!/2 = 60
        _ -> expectationFailure "Expected CF constructor"
      
    it "Alternating simple rule works for n >= 5" $ do
      let hyperThm = alternatingSimple
          inputFact = alternatingGroup "A5" "5"
          result = hyperTheoremRule hyperThm [inputFact]
          
      length result `shouldBe` 1
      case head result of
        CF f -> do
          factName f `shouldBe` "simple"
          factArgs f `shouldBe` ["A5"]
        _ -> expectationFailure "Expected CF constructor"
      
    it "Alternating simple rule doesn't apply for n < 5" $ do
      let hyperThm = alternatingSimple
          inputFact = alternatingGroup "A3" "3"
          result = hyperTheoremRule hyperThm [inputFact]
          
      length result `shouldBe` 0  -- A3 is not simple
      
    it "Divisibility contradiction detects non-divisors" $ do
      let hyperThm = dividesContradiction
          inputFact = divides "7" "12"  -- 7 does not divide 12
          result = hyperTheoremRule hyperThm [inputFact]
          
      length result `shouldBe` 1
      case head result of
        CF f -> factName f `shouldBe` "false"
        _ -> expectationFailure "Expected CF constructor"
      
    it "Divisibility contradiction allows actual divisors" $ do
      let hyperThm = dividesContradiction
          inputFact = divides "6" "12"  -- 6 divides 12
          result = hyperTheoremRule hyperThm [inputFact]
          
      length result `shouldBe` 0  -- No contradiction
      
  describe "Integration tests" $ do
    it "can set up a proof environment" $ do
      let facts = [group "G", order "G" "12"]
          theorems = [lagrange, simpleNotSimple]
          theoremDict = Map.fromList [(theoremName thm, thm) | thm <- theorems]
          goal = notSimple "G"
          env = createProofEnvironment facts theorems theoremDict goal
          
      length (peFacts env) `shouldBe` 2
      length (peTheorems env) `shouldBe` 2
      peGoalAchieved env `shouldBe` False