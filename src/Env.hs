module Env
  ( -- Re-export types
    FactEntry(..)
  , DisjunctionEntry(..)
  , Labeled(..)
  , ProofEnvironment(..)
  , NewConclusion(..)
  , FactDatabase(..)
  , GoalState(..)
  , GeneratorState(..)
  , CaseState(..)
  , Provenance(..)
  -- Backward compatibility accessors
  , feDependencies
  , feDisAncestors
  , feConcThm
  , deDisAncestors
  , deConcThm
  -- Main functions
  , initEnv
  -- Re-export accessors
  , module Environment.Accessors
  -- Re-export from sub-modules

  , module Environment.Goals
  , module Environment.Labels
  , module Environment.Symbols
  , module Environment.Variables
  ) where

-- Standard library
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Local modules
import Core
import Environment.Accessors
import Environment.FactsMonadic (addNewFactsM)
import ProofMonad (execProofM)

import Environment.Goals
import Environment.Labels
import Environment.Symbols
import Environment.Types
import Environment.Variables

-- Build trigger index for incremental theorem matching
buildTriggerIndex :: [Thm] -> TriggerIndex
buildTriggerIndex thms =
  let triggers = [ (factKey premise, TheoremTrigger thm i premises)
                 | thm <- thms
                 , let premises = thmFacts thm
                 , (i, premise) <- zip [0..] premises
                 ]
   in Map.fromListWith (++) [(k, [t]) | (k, t) <- triggers]

-- Initialize proof environment with initial facts, theorems, and goal
initEnv :: [Fact] -> [Thm] -> Map.Map String Thm -> Fact -> ProofEnvironment
initEnv facts theorems thmDict goal =
  let baseFactDB = FactDatabase
        { fdFacts = []
        , fdOrderedFacts = []
        , fdFactLabels = Map.empty
        , fdFactIndex = Map.empty
        , fdDisjunctions = []
        , fdDisjLabels = Map.empty
        }
      baseGoalState = GoalState
        { gsGoal = goal
        , gsAchieved = False
        , gsDisCombos = []
        }
      baseGenState = GeneratorState
        { gsCurFactNum = 0
        , gsCurDisjNum = 0
        , gsCurLetter = 'A'
        , gsCurSuffix = 0
        , gsSymbolSet = Set.empty
        }
      baseCaseState = CaseState
        { csCaseDepth = 0
        , csNumCases = 0
        , csSolvedCases = 0
        , csCaseDis = Nothing
        , csCaseFact = Nothing
        }
      triggerIndex = buildTriggerIndex theorems
      base = ProofEnvironment
        { peFactDB = baseFactDB
        , peGoalState = baseGoalState
        , peGenState = baseGenState
        , peCaseState = baseCaseState
        , peTheorems = theorems
        , peThmNameDict = thmDict
        , peTriggerIndex = triggerIndex
        }
      initialConcs =
        [ NewConclusion (CFact f) [] Set.empty Nothing | f <- facts
        ]
      envWithFacts = execProofM (addNewFactsM initialConcs) base
      initialSymbols =
        Set.fromList
          [ argText arg | Fact _ args <- facts, arg <- args ]
   in updateGenState (\gs -> gs { gsSymbolSet = initialSymbols }) envWithFacts
