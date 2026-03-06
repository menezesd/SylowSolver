{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StrictData #-}

-- | Core types for the proof environment.
--
-- The proof environment is organized into several components:
--
-- * 'FactDatabase' - Stores facts, disjunctions, and their indices
-- * 'GoalState' - Tracks the goal and disjunction coverage
-- * 'GeneratorState' - Manages ID generation and symbol tables
-- * 'CaseState' - Tracks case analysis depth and progress
--
-- The main type is 'ProofEnvironment', which composes these via
-- 'MatchState' (immutable matching structures) and 'BookkeepingState'
-- (mutable proof bookkeeping).
module Environment.Types
  ( FactDatabase(..)
  , GoalState(..)
  , CaseState(..)
  , GeneratorState(..)
  , EnvStats(..)
  , MatchState(..)
  , BookkeepingState(..)
  , ProofEnvironment(..)
  , FactEntry(..)
  , DisjunctionEntry(..)
  , DisjMeta(..)
  , Labeled(..)
  , NewConclusion(..)
  , Provenance(..)
  , DisjunctionKey(..)
  , mkDisjunctionKey
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
  , peFactDB
  , peFacts
  , peOrderedFacts
  , peFactLabels
  , peFactIndex
  , peDisjunctions
  , peDisjLabels
  , peDisjMeta
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
  , peSymbolTable
  , peSymbolNames
  , peNextSymbolId
  -- Case state accessors
  , peCaseDepth
  , peNumCases
  , peSolvedCases
  , peCaseDis
  , peCaseFact
  -- Trigger index accessor
  , peTriggerIndex
  -- Theorem accessors
  , peTheorems
  , peThmNameDict
  -- Update helpers
  , updateFactDB
  , updateGoalState
  , updateGenState
  , updateCaseState
  ) where

import Core
import Data.Map.Strict (Map)
import Data.IntMap.Strict (IntMap)
import Data.Set (Set)
import Data.Hashable (Hashable(..), hash)
import GHC.Generics (Generic)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Set as Set

-- TriggerIndex type alias for incremental theorem matching
-- Maps FactKey to list of TheoremTriggers
type TriggerIndex = HashMap.HashMap FactKey [TheoremTrigger]

-- Metadata for disjunctions to enable readable output
-- Tracks what variable/predicate the disjunction represents and branch values
data DisjMeta = DisjMeta
  { dmVarName :: String        -- e.g., "n₂" for num_sylow(2, G, _)
  , dmPredName :: PredName     -- The predicate that created this disjunction
  , dmBranchValues :: [String] -- Human-readable values for each branch
  } deriving stock (Eq, Show)

-- Provenance tracks how a fact or disjunction was derived
data Provenance = Provenance
  { provDeps :: [Label]
  , provDisAncestors :: Set (DisjId, Int)
  , provThm :: Maybe TheoremName
  } deriving stock (Eq, Show, Generic)

instance Hashable Provenance where
  hashWithSalt salt (Provenance deps ancs thm) =
    hashWithSalt salt (deps, Set.toList ancs, thm)

instance Semigroup Provenance where
  p1 <> p2 = Provenance
    { provDeps = provDeps p1 ++ provDeps p2
    , provDisAncestors = Set.union (provDisAncestors p1) (provDisAncestors p2)
    , provThm = provThm p1 <|> provThm p2
    }
    where
      Nothing <|> y = y
      x <|> _ = x

-- | A derived fact with full provenance information.
--
-- Each 'FactEntry' tracks:
--
-- * The fact itself ('feFact')
-- * A unique label for reference ('feLabel')
-- * Provenance (how it was derived, from which theorem)
-- * Whether it's useful for proving the goal ('feUseful')
-- * The case analysis depth where it was derived ('feDepth')
-- * Cached key and hash for efficient indexing
data FactEntry = FactEntry
  { feFact :: Fact           -- ^ The actual fact
  , feLabel :: FactId        -- ^ Unique identifier
  , feProv :: Provenance     -- ^ Derivation provenance
  , feUseful :: Bool         -- ^ Whether this fact contributes to the goal
  , feDepth :: !CaseDepth    -- ^ Case analysis depth
  , feHash :: HashKey        -- ^ Cached hash for index lookup
  } deriving stock (Eq, Show, Generic)

-- Backward compatibility accessors
feConcThm :: FactEntry -> Maybe TheoremName
feDependencies :: FactEntry -> [Label]
feDependencies = provDeps . feProv

feDisAncestors :: FactEntry -> Set (DisjId, Int)
feDisAncestors = provDisAncestors . feProv

feConcThm = provThm . feProv

-- | A disjunction (case split) in the proof.
--
-- Disjunctions represent case analysis: at least one of the 'deFacts'
-- must hold. During proof search, each branch is explored independently.
-- The goal is proven when all branches of all relevant disjunctions
-- have been covered.
data DisjunctionEntry = DisjunctionEntry
  { deFacts :: [Fact]        -- ^ The disjunction branches
  , deLabel :: DisjId        -- ^ Unique identifier
  , deProv :: Provenance     -- ^ Derivation provenance
  , deUseful :: Bool         -- ^ Whether this contributes to the goal
  , deHash :: HashKey        -- ^ Cached hash for deduplication
  } deriving stock (Eq, Show, Generic)

-- Backward compatibility accessors
deConcThm :: DisjunctionEntry -> Maybe TheoremName
deDisAncestors :: DisjunctionEntry -> Set (DisjId, Int)
deDisAncestors = provDisAncestors . deProv

deConcThm = provThm . deProv

data Labeled
  = LFactEntry FactEntry
  | LDisjEntry DisjunctionEntry
  deriving stock (Eq, Show)

-- Structural key for disjunction deduplication
-- Avoids string concatenation overhead
data DisjunctionKey = DisjunctionKey
  { dkFacts :: [(PredName, [Arg])]  -- Sorted facts by (name, args)
  , dkThm :: Maybe TheoremName
  , dkAncestors :: [(DisjId, Int)]  -- Sorted ancestors
  , dkHash :: {-# UNPACK #-} !Int   -- Cached hash for O(1) lookup
  } deriving stock (Eq, Ord, Show)

instance Hashable DisjunctionKey where
  hashWithSalt salt dk = hashWithSalt salt (dkHash dk)
  hash = dkHash

-- Smart constructor that computes and caches the hash
mkDisjunctionKey :: [(PredName, [Arg])] -> Maybe TheoremName -> [(DisjId, Int)] -> DisjunctionKey
mkDisjunctionKey facts thm ancestors =
  let h = hash (map (\(n, as) -> (predNameText n, as)) facts, fmap theoremNameText thm, ancestors)
   in DisjunctionKey facts thm ancestors h

-- | Database of all derived facts and disjunctions.
--
-- Provides multiple access patterns:
--
-- * 'fdFacts' - List of all facts (most recent first)
-- * 'fdFactIndex' - Hash-indexed lookup by fact signature
-- * 'fdFactLabels' - Label-based lookup for provenance tracking
data FactDatabase = FactDatabase
  { fdFacts :: ![FactEntry]                              -- ^ All facts (most recent first)
  , fdOrderedFacts :: ![Label]                           -- ^ Ordered list of all labels
  , fdFactLabels :: !(HashMap.HashMap Label Labeled)     -- ^ Label to entry mapping
  , fdFactIndex :: !(IntMap [FactEntry])                 -- ^ Hash-indexed fact lookup
  , fdDisjunctions :: ![DisjunctionEntry]                -- ^ All disjunctions
  , fdDisjLabels :: !(HashMap.HashMap DisjunctionKey DisjId) -- ^ Deduplication index
  , fdDisjMeta :: !(IntMap DisjMeta)                     -- ^ Human-readable metadata
  } deriving stock (Show)

-- | Tracks progress toward proving the goal.
--
-- The goal is achieved when all combinations of disjunction branches
-- have been covered (complete case analysis).
data GoalState = GoalState
  { gsGoal :: !Fact                         -- ^ The fact to prove
  , gsAchieved :: !Bool                     -- ^ Whether the goal has been proven
  , gsDisCombos :: ![Set (DisjId, Int)]     -- ^ Observed branch combinations
  , gsCachedDisjSizes :: !(Map DisjId Int)  -- ^ Cached disjunction sizes
  , gsCachedCombos :: !(Set (Set (DisjId, Int))) -- ^ Cached required combinations
  } deriving stock (Show)

-- | State for generating unique IDs and managing symbols.
data GeneratorState = GeneratorState
  { gsCurFactNum :: {-# UNPACK #-} !Int  -- ^ Next fact ID
  , gsCurDisjNum :: {-# UNPACK #-} !Int  -- ^ Next disjunction ID
  , gsCurLetter :: !Char                  -- ^ Current symbol letter (A-Z)
  , gsCurSuffix :: {-# UNPACK #-} !Int   -- ^ Current symbol suffix
  , gsSymbolTable :: Map String Symbol    -- ^ Name to Symbol mapping
  , gsSymbolNames :: IntMap String        -- ^ ID to name mapping
  , gsNextSymbolId :: !SymbolId           -- ^ Next symbol ID
  , gsStats :: !EnvStats                  -- ^ Running statistics
  } deriving stock (Show)

data EnvStats = EnvStats
  { esFacts :: {-# UNPACK #-} !Int
  , esDisjunctions :: {-# UNPACK #-} !Int
  , esSymbols :: {-# UNPACK #-} !Int
  } deriving stock (Eq, Show, Generic)

instance Semigroup EnvStats where
  EnvStats a b c <> EnvStats d e f = EnvStats (a + d) (b + e) (c + f)

instance Monoid EnvStats where
  mempty = EnvStats 0 0 0

-- | State for tracking case analysis progress.
data CaseState = CaseState
  { csCaseDepth :: !CaseDepth              -- ^ Current nesting depth
  , csNumCases :: {-# UNPACK #-} !Int      -- ^ Total number of cases
  , csSolvedCases :: {-# UNPACK #-} !Int   -- ^ Cases that reached a conclusion
  , csCaseDis :: Maybe DisjunctionEntry    -- ^ Current disjunction being split
  , csCaseFact :: Maybe FactEntry          -- ^ Current branch fact
  } deriving stock (Show)

-- | Immutable matching structures for efficient theorem triggering.
data MatchState = MatchState
  { msFactDB :: !FactDatabase       -- ^ The fact database
  , msTriggerIndex :: !TriggerIndex -- ^ Pre-built theorem trigger index
  }

instance Show MatchState where
  show _ = "MatchState"

-- | Mutable proof bookkeeping state.
data BookkeepingState = BookkeepingState
  { bsGoalState :: !GoalState                           -- ^ Goal tracking
  , bsCaseState :: !CaseState                           -- ^ Case analysis state
  , bsGenState :: !GeneratorState                       -- ^ ID/symbol generation
  , bsTheorems :: ![Thm]                                -- ^ Available theorems
  , bsThmNameDict :: !(HashMap.HashMap TheoremName Thm) -- ^ Theorem lookup by name
  } deriving stock (Show)

-- | The main proof environment.
--
-- Composed of:
--
-- * 'peMatch' - Immutable matching structures (fact database, trigger index)
-- * 'peBook' - Mutable bookkeeping (goal, case state, generators)
--
-- Use the accessor functions (e.g., 'peFacts', 'peGoal') rather than
-- drilling into the internal structure directly.
data ProofEnvironment = ProofEnvironment
  { peMatch :: !MatchState        -- ^ Matching structures
  , peBook :: !BookkeepingState   -- ^ Bookkeeping state
  } deriving stock (Show)

-- | A new conclusion to be added to the proof environment.
--
-- Includes the conclusion itself plus provenance information:
-- which facts it depends on, which disjunction branches it came from,
-- and which theorem (if any) derived it.
data NewConclusion = NewConclusion
  { ncConclusion :: Conclusion         -- ^ The fact or disjunction to add
  , ncDependencies :: [Label]          -- ^ Facts this depends on
  , ncDisAncestors :: Set (DisjId, Int) -- ^ Disjunction branches in scope
  , ncConcThm :: Maybe TheoremName     -- ^ The deriving theorem
  }

-- | Create a Provenance from a NewConclusion
mkProvenance :: NewConclusion -> Provenance
mkProvenance nc = Provenance
  { provDeps = ncDependencies nc
  , provDisAncestors = ncDisAncestors nc
  , provThm = ncConcThm nc
  }

-- Access helpers for nested state
{-# INLINE peFactDB #-}
peFactDB :: ProofEnvironment -> FactDatabase
peFactDB = msFactDB . peMatch

{-# INLINE peTriggerIndex #-}
peTriggerIndex :: ProofEnvironment -> TriggerIndex
peTriggerIndex = msTriggerIndex . peMatch

{-# INLINE peGoalState #-}
peGoalState :: ProofEnvironment -> GoalState
peGoalState = bsGoalState . peBook

{-# INLINE peCaseState #-}
peCaseState :: ProofEnvironment -> CaseState
peCaseState = bsCaseState . peBook

{-# INLINE peGenState #-}
peGenState :: ProofEnvironment -> GeneratorState
peGenState = bsGenState . peBook

{-# INLINE peTheorems #-}
peTheorems :: ProofEnvironment -> [Thm]
peTheorems = bsTheorems . peBook

{-# INLINE peThmNameDict #-}
peThmNameDict :: ProofEnvironment -> HashMap.HashMap TheoremName Thm
peThmNameDict = bsThmNameDict . peBook

-- FactDatabase accessors
{-# INLINE peFacts #-}
peFacts :: ProofEnvironment -> [FactEntry]
peFacts = fdFacts . peFactDB

{-# INLINE peOrderedFacts #-}
peOrderedFacts :: ProofEnvironment -> [Label]
peOrderedFacts = fdOrderedFacts . peFactDB

{-# INLINE peFactLabels #-}
peFactLabels :: ProofEnvironment -> HashMap.HashMap Label Labeled
peFactLabels = fdFactLabels . peFactDB

{-# INLINE peFactIndex #-}
peFactIndex :: ProofEnvironment -> IntMap [FactEntry]
peFactIndex = fdFactIndex . peFactDB

{-# INLINE peDisjunctions #-}
peDisjunctions :: ProofEnvironment -> [DisjunctionEntry]
peDisjunctions = fdDisjunctions . peFactDB

{-# INLINE peDisjLabels #-}
peDisjLabels :: ProofEnvironment -> HashMap.HashMap DisjunctionKey DisjId
peDisjLabels = fdDisjLabels . peFactDB

{-# INLINE peDisjMeta #-}
peDisjMeta :: ProofEnvironment -> IntMap DisjMeta
peDisjMeta = fdDisjMeta . peFactDB

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
peGoalCachedCombos :: ProofEnvironment -> Set (Set (DisjId, Int))
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

{-# INLINE peSymbolTable #-}
peSymbolTable :: ProofEnvironment -> Map String Symbol
peSymbolTable = gsSymbolTable . peGenState

{-# INLINE peSymbolNames #-}
peSymbolNames :: ProofEnvironment -> IntMap String
peSymbolNames = gsSymbolNames . peGenState

{-# INLINE peNextSymbolId #-}
peNextSymbolId :: ProofEnvironment -> SymbolId
peNextSymbolId = gsNextSymbolId . peGenState

-- CaseState accessors
{-# INLINE peCaseDepth #-}
peCaseDepth :: ProofEnvironment -> CaseDepth
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
-- Update helpers
{-# INLINE updateFactDB #-}
updateFactDB :: (FactDatabase -> FactDatabase) -> ProofEnvironment -> ProofEnvironment
updateFactDB f env =
  env { peMatch = (peMatch env) { msFactDB = f (msFactDB (peMatch env)) } }

{-# INLINE updateGoalState #-}
updateGoalState :: (GoalState -> GoalState) -> ProofEnvironment -> ProofEnvironment
updateGoalState f env =
  env { peBook = (peBook env) { bsGoalState = f (bsGoalState (peBook env)) } }

{-# INLINE updateGenState #-}
updateGenState :: (GeneratorState -> GeneratorState) -> ProofEnvironment -> ProofEnvironment
updateGenState f env =
  env { peBook = (peBook env) { bsGenState = f (bsGenState (peBook env)) } }

{-# INLINE updateCaseState #-}
updateCaseState :: (CaseState -> CaseState) -> ProofEnvironment -> ProofEnvironment
updateCaseState f env =
  env { peBook = (peBook env) { bsCaseState = f (bsCaseState (peBook env)) } }
