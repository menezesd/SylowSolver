-- | Core.hs
--
-- Core data-model types for the theorem prover.
-- This module contains the Fact, Disjunction, Theorem, and HyperTheorem
-- data types, ported from the Python core.py module.

{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE DeriveGeneric #-}

module Core
  ( Fact(..)
  , Disjunction(..)
  , Theorem(..)
  , HyperTheorem(..)
  , Conclusion(..)
  , FactLabel
  , DisjunctionAncestor
  , Arguments
  , createFact
  , createDisjunction
  , createTheorem
  , createHyperTheorem
  , factEquals
  , copyFact
  ) where

import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic)

-- | Type aliases for clarity
type FactLabel = String
type Arguments = [String]
type DisjunctionAncestor = (String, Int)  -- (DisjunctionLabel, disjunctionIndex)

-- | A simple fact object: (name, args) with provenance metadata.
-- Corresponds to the Python Fact class.
data Fact = Fact
  { factName :: String
  , factArgs :: Arguments
  , factDependencies :: [FactLabel]  -- facts needed to conclude this fact
  , factLabel :: Maybe FactLabel
  , factDisAncestors :: Set DisjunctionAncestor  -- disjunction facts needed
  , factDepth :: Int  -- number of nested cases where fact was shown
  , factUseful :: Bool  -- was this fact used to conclude the goal
  , factConcludingTheorem :: Maybe String  -- theorem that concluded this fact
  } deriving (Show, Eq, Ord, Generic)

-- | Represents a disjunction of Fact objects.
-- Each Disjunction contains a list of Fact instances representing alternatives.
data Disjunction = Disjunction
  { disjunctionFacts :: [Fact]
  , disjunctionDependencies :: [FactLabel]
  , disjunctionDisAncestors :: Set DisjunctionAncestor
  , disjunctionLabel :: Maybe String
  , disjunctionUseful :: Bool
  , disjunctionConcludingTheorem :: Maybe String
  } deriving (Show, Eq, Generic)

-- | A declarative theorem: pattern of input facts -> concrete conclusions.
data Theorem = Theorem
  { theoremInputFacts :: [Fact]  -- pattern of input facts
  , theoremConclusions :: [Fact]  -- concrete conclusions
  , theoremName :: String
  } deriving (Show, Eq, Ord, Generic)

-- | A theorem backed by a rule function that produces conclusions.
-- The rule function takes facts matching the input pattern and produces new facts.
data HyperTheorem = HyperTheorem
  { hyperTheoremInputFacts :: [Fact]  -- pattern of input facts
  , hyperTheoremRule :: [Fact] -> [Conclusion]  -- rule function
  , hyperTheoremName :: String
  , hyperTheoremMultiArgs :: Bool  -- can the theorem take multiple arguments?
  }

-- Note: HyperTheorem doesn't derive Show/Eq because of the function field

-- | Smart constructor for Fact with sensible defaults.
createFact :: String -> Arguments -> Fact
createFact name args = Fact
  { factName = name
  , factArgs = args
  , factDependencies = []
  , factLabel = Nothing
  , factDisAncestors = Set.empty
  , factDepth = 0
  , factUseful = False
  , factConcludingTheorem = Nothing
  }

-- | Smart constructor for Disjunction with sensible defaults.
createDisjunction :: [Fact] -> Disjunction
createDisjunction facts = Disjunction
  { disjunctionFacts = facts
  , disjunctionDependencies = []
  , disjunctionDisAncestors = Set.empty
  , disjunctionLabel = Nothing
  , disjunctionUseful = False
  , disjunctionConcludingTheorem = Nothing
  }

-- | Smart constructor for Theorem.
createTheorem :: [Fact] -> [Fact] -> String -> Theorem
createTheorem inputFacts conclusions name = Theorem
  { theoremInputFacts = inputFacts
  , theoremConclusions = conclusions
  , theoremName = name
  }

-- | Smart constructor for HyperTheorem.
createHyperTheorem :: [Fact] -> ([Fact] -> [Conclusion]) -> String -> HyperTheorem
createHyperTheorem inputFacts rule name = HyperTheorem
  { hyperTheoremInputFacts = inputFacts
  , hyperTheoremRule = rule
  , hyperTheoremName = name
  , hyperTheoremMultiArgs = False
  }

-- | Check if two facts are equal (same name and arguments).
factEquals :: Fact -> Fact -> Bool
factEquals f1 f2 = factName f1 == factName f2 && factArgs f1 == factArgs f2

-- | Create a shallow copy of a fact preserving metadata.
copyFact :: Fact -> Fact
copyFact fact = fact
  { factArgs = factArgs fact  -- Lists are immutable in Haskell, no need for explicit copy
  , factDependencies = factDependencies fact
  , factDisAncestors = factDisAncestors fact
  }

-- | A conclusion produced by a rule: either a Fact or a Disjunction of facts
data Conclusion
  = CF Fact
  | CD Disjunction
  deriving (Show, Eq, Generic)