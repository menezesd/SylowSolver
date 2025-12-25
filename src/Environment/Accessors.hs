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
peFacts :: ProofEnvironment -> [FactEntry]
peFacts = fdFacts . peFactDB

peOrderedFacts :: ProofEnvironment -> [Label]
peOrderedFacts = fdOrderedFacts . peFactDB

peFactLabels :: ProofEnvironment -> Map Label Labeled
peFactLabels = fdFactLabels . peFactDB

peFactIndex :: ProofEnvironment -> Map FactKey [FactEntry]
peFactIndex = fdFactIndex . peFactDB

peDisjunctions :: ProofEnvironment -> [DisjunctionEntry]
peDisjunctions = fdDisjunctions . peFactDB

peDisjLabels :: ProofEnvironment -> Map DisjunctionKey DisjId
peDisjLabels = fdDisjLabels . peFactDB

-- GoalState accessors
peGoal :: ProofEnvironment -> Fact
peGoal = gsGoal . peGoalState

peGoalAchieved :: ProofEnvironment -> Bool
peGoalAchieved = gsAchieved . peGoalState

peGoalDisCombos :: ProofEnvironment -> [Set (DisjId, Int)]
peGoalDisCombos = gsDisCombos . peGoalState

-- GeneratorState accessors
peCurFactNum :: ProofEnvironment -> Int
peCurFactNum = gsCurFactNum . peGenState

peCurDisjNum :: ProofEnvironment -> Int
peCurDisjNum = gsCurDisjNum . peGenState

peCurLetter :: ProofEnvironment -> Char
peCurLetter = gsCurLetter . peGenState

peCurSuffix :: ProofEnvironment -> Int
peCurSuffix = gsCurSuffix . peGenState

peSymbolSet :: ProofEnvironment -> Set String
peSymbolSet = gsSymbolSet . peGenState

-- CaseState accessors
peCaseDepth :: ProofEnvironment -> Int
peCaseDepth = csCaseDepth . peCaseState

peNumCases :: ProofEnvironment -> Int
peNumCases = csNumCases . peCaseState

peSolvedCases :: ProofEnvironment -> Int
peSolvedCases = csSolvedCases . peCaseState

peCaseDis :: ProofEnvironment -> Maybe DisjunctionEntry
peCaseDis = csCaseDis . peCaseState

peCaseFact :: ProofEnvironment -> Maybe FactEntry
peCaseFact = csCaseFact . peCaseState

-- Trigger index accessor
peTriggerIndexAccessor :: ProofEnvironment -> TriggerIndex
peTriggerIndexAccessor env = peTriggerIndex env

-- Update helpers
updateFactDB :: (FactDatabase -> FactDatabase) -> ProofEnvironment -> ProofEnvironment
updateFactDB f env = env { peFactDB = f (peFactDB env) }

updateGoalState :: (GoalState -> GoalState) -> ProofEnvironment -> ProofEnvironment
updateGoalState f env = env { peGoalState = f (peGoalState env) }

updateGenState :: (GeneratorState -> GeneratorState) -> ProofEnvironment -> ProofEnvironment
updateGenState f env = env { peGenState = f (peGenState env) }

updateCaseState :: (CaseState -> CaseState) -> ProofEnvironment -> ProofEnvironment
updateCaseState f env = env { peCaseState = f (peCaseState env) }
