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
  -- Constructors / helpers
  , initEnv
  , addNewFacts
  , updateGoalState
  , updateGoalAchieved
  -- Backward compatibility accessors
  , feDependencies
  , feDisAncestors
  , feConcThm
  , deDisAncestors
  , deConcThm
  -- Main functions

  -- Re-export accessors
  , peFacts
  , peDisjunctions
  , peGoalAchieved
  , peTriggerIndex
  , peFactDB
  ) where

import Environment.Types
import Environment.Init (initEnv)
import Environment.FactsMonadic (addNewFactsM)
import Environment.Goals (updateGoalAchieved)
import ProofMonad (runProofM)

-- Pure wrapper around monadic fact insertion for tests/benchmarks
addNewFacts :: ProofEnvironment -> [NewConclusion] -> (ProofEnvironment, [FactEntry])
addNewFacts env concs =
  let (facts, env') = runProofM (addNewFactsM concs) env
   in (env', facts)
