{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StrictData #-}

module Environment.Types
  ( FactDatabase(..)
  , GoalState(..)
  , CaseState(..)
  , GeneratorState(..)
  , ProofEnvironment(..)
  , FactEntry(..)
  , DisjunctionEntry(..)
  , Labeled(..)
  , NewConclusion(..)
  , Provenance(..)
  , DisjunctionKey(..)
  , TriggerIndex
  -- Helper functions
  , mkProvenance
  -- Backward compatibility accessors
  , feDependencies
  , feDisAncestors
  , feConcThm
  , deDisAncestors
  , deConcThm
  ) where

import Core
import Data.Map.Strict (Map)
import Data.Set (Set)

-- TriggerIndex type alias for incremental theorem matching
-- Maps FactKey to list of TheoremTriggers
type TriggerIndex = Map FactKey [TheoremTrigger]

-- Provenance tracks how a fact or disjunction was derived
data Provenance = Provenance
  { provDeps :: [Label]
  , provDisAncestors :: Set (DisjId, Int)
  , provThm :: Maybe String
  } deriving stock (Eq, Show)

-- Entries that track facts and disjunctions with metadata
data FactEntry = FactEntry
  { feFact :: Fact
  , feLabel :: FactId
  , feProv :: Provenance
  , feUseful :: Bool
  , feDepth :: Int
  } deriving stock (Eq, Show)

-- Backward compatibility accessors
feDependencies :: FactEntry -> [Label]
feDependencies = provDeps . feProv

feDisAncestors :: FactEntry -> Set (DisjId, Int)
feDisAncestors = provDisAncestors . feProv

feConcThm :: FactEntry -> Maybe String
feConcThm = provThm . feProv

data DisjunctionEntry = DisjunctionEntry
  { deFacts :: [Fact]
  , deLabel :: DisjId
  , deProv :: Provenance
  , deUseful :: Bool
  } deriving stock (Eq, Show)

-- Backward compatibility accessors
deDisAncestors :: DisjunctionEntry -> Set (DisjId, Int)
deDisAncestors = provDisAncestors . deProv

deConcThm :: DisjunctionEntry -> Maybe String
deConcThm = provThm . deProv

data Labeled
  = LFactEntry FactEntry
  | LDisjEntry DisjunctionEntry
  deriving stock (Eq, Show)

-- Structural key for disjunction deduplication
-- Avoids string concatenation overhead
data DisjunctionKey = DisjunctionKey
  { dkFacts :: [(String, [Arg])]  -- Sorted facts by (name, args)
  , dkThm :: Maybe String
  , dkAncestors :: [(DisjId, Int)]  -- Sorted ancestors
  } deriving stock (Eq, Ord, Show)

-- Database of all facts and disjunctions
data FactDatabase = FactDatabase
  { fdFacts :: [FactEntry]
  , fdOrderedFacts :: [Label]
  , fdFactLabels :: Map Label Labeled
  , fdFactIndex :: Map FactKey [FactEntry]
  , fdDisjunctions :: [DisjunctionEntry]
  , fdDisjLabels :: Map DisjunctionKey DisjId
  } deriving stock (Show)

-- Goal tracking state
data GoalState = GoalState
  { gsGoal :: Fact
  , gsAchieved :: Bool
  , gsDisCombos :: [Set (DisjId, Int)]
  } deriving stock (Show)

-- Generator state for IDs and symbols
data GeneratorState = GeneratorState
  { gsCurFactNum :: Int
  , gsCurDisjNum :: Int
  , gsCurLetter :: Char
  , gsCurSuffix :: Int
  , gsSymbolSet :: Set String
  } deriving stock (Show)

-- Case analysis state
data CaseState = CaseState
  { csCaseDepth :: Int
  , csNumCases :: Int
  , csSolvedCases :: Int
  , csCaseDis :: Maybe DisjunctionEntry
  , csCaseFact :: Maybe FactEntry
  } deriving stock (Show)

-- Main proof environment with organized sub-structures
data ProofEnvironment = ProofEnvironment
  { peFactDB :: FactDatabase
  , peGoalState :: GoalState
  , peCaseState :: CaseState
  , peGenState :: GeneratorState
  , peTheorems :: [Thm]
  , peThmNameDict :: Map String Thm
  , peTriggerIndex :: TriggerIndex
    -- ^ Index for incremental theorem matching
    -- Stores TheoremTrigger for each FactKey
  }

-- New conclusions to be added
data NewConclusion = NewConclusion
  { ncConclusion :: Conclusion
  , ncDependencies :: [Label]
  , ncDisAncestors :: Set (DisjId, Int)
  , ncConcThm :: Maybe String
  }

-- | Create a Provenance from a NewConclusion
mkProvenance :: NewConclusion -> Provenance
mkProvenance nc = Provenance
  { provDeps = ncDependencies nc
  , provDisAncestors = ncDisAncestors nc
  , provThm = ncConcThm nc
  }
