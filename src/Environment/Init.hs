module Environment.Init
  ( initEnv
  ) where

import Core
import Environment.Types
import Environment.FactsMonadic (addNewFactsM)
import ProofMonad (execProofM)
import Theorems (buildTriggerIndex)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set

-- Initialize proof environment with initial facts, theorems, and goal
initEnv :: [Fact] -> [Thm] -> HashMap.HashMap TheoremName Thm -> Fact -> ProofEnvironment
initEnv facts theorems thmDict goal =
  let baseFactDB = FactDatabase
        { fdFacts = []
        , fdOrderedFacts = []
        , fdFactLabels = Map.empty
        , fdFactIndex = IntMap.empty
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
        , gsSymbolTable = Map.empty
        , gsSymbolNames = IntMap.empty
        , gsNextSymbolId = 0
        , gsStats = EnvStats 0 0 0
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
   in execProofM (addNewFactsM initialConcs) base
