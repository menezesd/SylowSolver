module Environment.Accessors
  ( -- Fact database accessors
    peFacts
  , peOrderedFacts
  , peFactLabels
  , peFactIndex
  , peDisjunctions
  , peDisjLabels
  -- Goal state accessors
  , peGoal
  , peGoalAchieved
  , peGoalDisCombos
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

import Environment.Types
import Core
import Data.Map.Strict (Map)
import Data.Set (Set)

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
