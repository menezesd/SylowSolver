{-# LANGUAGE TemplateHaskell #-}

-- This module generates lenses for Environment types using Template Haskell.
-- All generated lenses and re-exported lens operators are available.

module Environment.Lenses where

import Lens.Micro
import Lens.Micro.Mtl
import Lens.Micro.TH (makeLenses)
import Environment.Types

-- Generate lenses for all record types
-- By default, makeLenses creates lenses by dropping the prefix and lowercasing
--
-- FactDatabase: fdXxx → xxx
--   facts, orderedFacts, factLabels, factIndex, disjunctions, disjLabels
--
-- GoalState: gsXxx → xxx
--   goal, achieved, disCombos
--
-- GeneratorState: gsXxx → xxx
--   curFactNum, curDisjNum, curLetter, curSuffix, symbolSet
--
-- CaseState: csXxx → xxx
--   caseDepth, numCases, solvedCases, caseDis, caseFact
--
-- ProofEnvironment: peXxx → xxx
--   factDB, goalState, caseState, genState, theorems, thmNameDict
--
-- FactEntry: feXxx → xxx
--   fact, label, dependencies, disAncestors, concThm, useful, depth

makeLenses ''FactDatabase
makeLenses ''GoalState
makeLenses ''GeneratorState
makeLenses ''CaseState
makeLenses ''ProofEnvironment
makeLenses ''FactEntry
