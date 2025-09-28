-- | CoreSpec.hs
--
-- Tests for the Core module data structures.

module CoreSpec where

import Test.Hspec
import Core
import Data.Set (Set)
import qualified Data.Set as Set

spec :: Spec
spec = do
  describe "Fact" $ do
    it "creates facts with correct fields" $ do
      let fact = createFact "group" ["G"]
      factName fact `shouldBe` "group"
      factArgs fact `shouldBe` ["G"]
      factDependencies fact `shouldBe` []
      factUseful fact `shouldBe` False
      
    it "supports equality checking" $ do
      let fact1 = createFact "group" ["G"]
          fact2 = createFact "group" ["G"]  
          fact3 = createFact "group" ["H"]
          fact4 = createFact "order" ["G"]
      factEquals fact1 fact2 `shouldBe` True
      factEquals fact1 fact3 `shouldBe` False
      factEquals fact1 fact4 `shouldBe` False
      
    it "supports copying with metadata preservation" $ do
      let originalFact = (createFact "group" ["G"]) 
            { factUseful = True
            , factDepth = 2
            , factDependencies = ["F1", "F2"]
            }
          copiedFact = copyFact originalFact
      factUseful copiedFact `shouldBe` True
      factDepth copiedFact `shouldBe` 2
      factDependencies copiedFact `shouldBe` ["F1", "F2"]
      
  describe "Disjunction" $ do
    it "creates disjunctions with multiple facts" $ do
      let fact1 = createFact "group" ["G"]
          fact2 = createFact "simple" ["G"]
          disj = createDisjunction [fact1, fact2]
      length (disjunctionFacts disj) `shouldBe` 2
      disjunctionUseful disj `shouldBe` False
      
  describe "Theorem" $ do
    it "creates theorems with input and output facts" $ do
      let inputFacts = [createFact "group" ["G"]]
          outputFacts = [createFact "simple" ["G"]]
          thm = createTheorem inputFacts outputFacts "test_theorem"
      theoremName thm `shouldBe` "test_theorem"
      length (theoremInputFacts thm) `shouldBe` 1
      length (theoremConclusions thm) `shouldBe` 1
      
  describe "HyperTheorem" $ do
    it "creates hyper-theorems with rule functions" $ do
      let inputFacts = [createFact "group" ["G"]]
          rule facts = [CF (createFact "simple" [head (factArgs (head facts))])]
          hyperThm = createHyperTheorem inputFacts rule "test_hyper"
      hyperTheoremName hyperThm `shouldBe` "test_hyper"
      hyperTheoremMultiArgs hyperThm `shouldBe` False
      -- Test rule application
      let testFact = createFact "group" ["TestGroup"]
          result = hyperTheoremRule hyperThm [testFact]
      length result `shouldBe` 1
      case head result of
        CF f -> do
          factName f `shouldBe` "simple"
          factArgs f `shouldBe` ["TestGroup"]
        _ -> expectationFailure "Expected CF constructor"