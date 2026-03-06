module Environment.Init
  ( initEnv
  ) where

import Core
import Environment.Types
import Environment.FactsMonadic (addNewFactsM)
import ProofMonad (execProofM)
import Theorems (buildTriggerIndex)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Initialize proof environment with initial facts, theorems, and goal
initEnv :: [Fact] -> [Thm] -> HashMap.HashMap TheoremName Thm -> Fact -> ProofEnvironment
initEnv facts theorems thmDict goal =
  let baseFactDB = FactDatabase
        { fdFacts = []
        , fdOrderedFacts = []
        , fdFactLabels = HashMap.empty
        , fdFactIndex = IntMap.empty
        , fdDisjunctions = []
        , fdDisjLabels = HashMap.empty
        , fdDisjMeta = IntMap.empty
        }
      baseGoalState = GoalState
        { gsGoal = goal
        , gsAchieved = False
        , gsDisCombos = []
        , gsCachedDisjSizes = Map.empty
        , gsCachedCombos = mempty
        }
      baseGenState = GeneratorState
        { gsCurFactNum = 0
        , gsCurDisjNum = 0
        , gsCurLetter = 'A'
        , gsCurSuffix = 0
        , gsSymbolTable = Map.empty
        , gsSymbolNames = IntMap.empty
        , gsNextSymbolId = SymbolId 0
        , gsStats = EnvStats 0 0 0
        }
      baseCaseState = CaseState
        { csCaseDepth = CaseDepth 0
        , csNumCases = 0
        , csSolvedCases = 0
        , csCaseDis = Nothing
        , csCaseFact = Nothing
        }
      triggerIndex = buildTriggerIndex theorems
      baseMatch = MatchState
        { msFactDB = baseFactDB
        , msTriggerIndex = triggerIndex
        }
      baseBook = BookkeepingState
        { bsGoalState = baseGoalState
        , bsCaseState = baseCaseState
        , bsGenState = baseGenState
        , bsTheorems = theorems
        , bsThmNameDict = thmDict
        }
      base = ProofEnvironment
        { peMatch = baseMatch
        , peBook = baseBook
        }
      initialConcs =
        [ NewConclusion (CFact f) [] Set.empty Nothing | f <- facts
        ]
   in execProofM (addNewFactsM initialConcs) base
