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
  -- Fact database accessors
  , peFacts
  , peOrderedFacts
  , peFactLabels
  , peFactIndex
  , peDisjunctions
  , peDisjLabels
  -- Goal state accessors
  , peGoal
  , peGoalAchieved
  , peGoalDisCombos
  , peGoalCachedDisjSizes
  , peGoalCachedCombos
  -- Generator state accessors
  , peCurFactNum
  , peCurDisjNum
  , peCurLetter
  , peCurSuffix
  , peSymbolSet
  -- Case state accessors
  , peCaseDepth
  , peNumCases
  , peSolvedCases
  , peCaseDis
  , peCaseFact
  -- Trigger index accessor
  , peTriggerIndexAccessor
  -- Update helpers
  , updateFactDB
  , updateGoalState
  , updateGenState
  , updateCaseState
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
  , gsCachedDisjSizes :: Map DisjId Int
  , gsCachedCombos :: [Set (DisjId, Int)]
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

-- FactDatabase accessors
{-# INLINE peFacts #-}
peFacts :: ProofEnvironment -> [FactEntry]
peFacts = fdFacts . peFactDB

{-# INLINE peOrderedFacts #-}
peOrderedFacts :: ProofEnvironment -> [Label]
peOrderedFacts = fdOrderedFacts . peFactDB

{-# INLINE peFactLabels #-}
peFactLabels :: ProofEnvironment -> Map Label Labeled
peFactLabels = fdFactLabels . peFactDB

{-# INLINE peFactIndex #-}
peFactIndex :: ProofEnvironment -> Map FactKey [FactEntry]
peFactIndex = fdFactIndex . peFactDB

{-# INLINE peDisjunctions #-}
peDisjunctions :: ProofEnvironment -> [DisjunctionEntry]
peDisjunctions = fdDisjunctions . peFactDB

{-# INLINE peDisjLabels #-}
peDisjLabels :: ProofEnvironment -> Map DisjunctionKey DisjId
peDisjLabels = fdDisjLabels . peFactDB

-- GoalState accessors
{-# INLINE peGoal #-}
peGoal :: ProofEnvironment -> Fact
peGoal = gsGoal . peGoalState

{-# INLINE peGoalAchieved #-}
peGoalAchieved :: ProofEnvironment -> Bool
peGoalAchieved = gsAchieved . peGoalState

{-# INLINE peGoalDisCombos #-}
peGoalDisCombos :: ProofEnvironment -> [Set (DisjId, Int)]
peGoalDisCombos = gsDisCombos . peGoalState

{-# INLINE peGoalCachedDisjSizes #-}
peGoalCachedDisjSizes :: ProofEnvironment -> Map DisjId Int
peGoalCachedDisjSizes = gsCachedDisjSizes . peGoalState

{-# INLINE peGoalCachedCombos #-}
peGoalCachedCombos :: ProofEnvironment -> [Set (DisjId, Int)]
peGoalCachedCombos = gsCachedCombos . peGoalState

-- GeneratorState accessors
{-# INLINE peCurFactNum #-}
peCurFactNum :: ProofEnvironment -> Int
peCurFactNum = gsCurFactNum . peGenState

{-# INLINE peCurDisjNum #-}
peCurDisjNum :: ProofEnvironment -> Int
peCurDisjNum = gsCurDisjNum . peGenState

{-# INLINE peCurLetter #-}
peCurLetter :: ProofEnvironment -> Char
peCurLetter = gsCurLetter . peGenState

{-# INLINE peCurSuffix #-}
peCurSuffix :: ProofEnvironment -> Int
peCurSuffix = gsCurSuffix . peGenState

{-# INLINE peSymbolSet #-}
peSymbolSet :: ProofEnvironment -> Set String
peSymbolSet = gsSymbolSet . peGenState

-- CaseState accessors
{-# INLINE peCaseDepth #-}
peCaseDepth :: ProofEnvironment -> Int
peCaseDepth = csCaseDepth . peCaseState

{-# INLINE peNumCases #-}
peNumCases :: ProofEnvironment -> Int
peNumCases = csNumCases . peCaseState

{-# INLINE peSolvedCases #-}
peSolvedCases :: ProofEnvironment -> Int
peSolvedCases = csSolvedCases . peCaseState

{-# INLINE peCaseDis #-}
peCaseDis :: ProofEnvironment -> Maybe DisjunctionEntry
peCaseDis = csCaseDis . peCaseState

{-# INLINE peCaseFact #-}
peCaseFact :: ProofEnvironment -> Maybe FactEntry
peCaseFact = csCaseFact . peCaseState

-- Trigger index accessor
{-# INLINE peTriggerIndexAccessor #-}
peTriggerIndexAccessor :: ProofEnvironment -> TriggerIndex
peTriggerIndexAccessor = peTriggerIndex

-- Update helpers
{-# INLINE updateFactDB #-}
updateFactDB :: (FactDatabase -> FactDatabase) -> ProofEnvironment -> ProofEnvironment
updateFactDB f env = env { peFactDB = f (peFactDB env) }

{-# INLINE updateGoalState #-}
updateGoalState :: (GoalState -> GoalState) -> ProofEnvironment -> ProofEnvironment
updateGoalState f env = env { peGoalState = f (peGoalState env) }

{-# INLINE updateGenState #-}
updateGenState :: (GeneratorState -> GeneratorState) -> ProofEnvironment -> ProofEnvironment
updateGenState f env = env { peGenState = f (peGenState env) }

{-# INLINE updateCaseState #-}
updateCaseState :: (CaseState -> CaseState) -> ProofEnvironment -> ProofEnvironment
updateCaseState f env = env { peCaseState = f (peCaseState env) }
