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
  -- Backward compatibility accessors
  , feDependencies
  , feDisAncestors
  , feConcThm
  , deDependencies
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
  } deriving (Eq, Show)

-- Entries that track facts and disjunctions with metadata
data FactEntry = FactEntry
  { feFact :: Fact
  , feLabel :: FactId
  , feProv :: Provenance
  , feUseful :: Bool
  , feDepth :: Int
  } deriving (Eq, Show)

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
  } deriving (Eq, Show)

-- Backward compatibility accessors
deDependencies :: DisjunctionEntry -> [Label]
deDependencies = provDeps . deProv

deDisAncestors :: DisjunctionEntry -> Set (DisjId, Int)
deDisAncestors = provDisAncestors . deProv

deConcThm :: DisjunctionEntry -> Maybe String
deConcThm = provThm . deProv

data Labeled
  = LFactEntry FactEntry
  | LDisjEntry DisjunctionEntry
  deriving (Eq, Show)

-- Structural key for disjunction deduplication
-- Avoids string concatenation overhead
data DisjunctionKey = DisjunctionKey
  { dkFacts :: [(String, [Arg])]  -- Sorted facts by (name, args)
  , dkThm :: Maybe String
  , dkAncestors :: [(DisjId, Int)]  -- Sorted ancestors
  } deriving (Eq, Ord, Show)

-- Database of all facts and disjunctions
data FactDatabase = FactDatabase
  { fdFacts :: [FactEntry]
  , fdOrderedFacts :: [Label]
  , fdFactLabels :: Map Label Labeled
  , fdFactIndex :: Map FactKey [FactEntry]
  , fdDisjunctions :: [DisjunctionEntry]
  , fdDisjLabels :: Map DisjunctionKey DisjId
  } deriving (Show)

-- Goal tracking state
data GoalState = GoalState
  { gsGoal :: Fact
  , gsAchieved :: Bool
  , gsDisCombos :: [Set (DisjId, Int)]
  } deriving (Show)

-- Generator state for IDs and symbols
data GeneratorState = GeneratorState
  { gsCurFactNum :: Int
  , gsCurDisjNum :: Int
  , gsCurLetter :: Char
  , gsCurSuffix :: Int
  , gsSymbolSet :: Set String
  } deriving (Show)

-- Case analysis state
data CaseState = CaseState
  { csCaseDepth :: Int
  , csNumCases :: Int
  , csSolvedCases :: Int
  , csCaseDis :: Maybe DisjunctionEntry
  , csCaseFact :: Maybe FactEntry
  } deriving (Show)

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
