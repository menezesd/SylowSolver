module Environment.Init
  ( initEnv
  ) where

import Core
import Environment.Types
import Environment.FactsMonadic (addNewFactsM)
import ProofMonad (execProofM)
import Theorems (buildTriggerIndex)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

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
        , gsCachedDisjSizes = Map.empty
        , gsCachedCombos = []
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
