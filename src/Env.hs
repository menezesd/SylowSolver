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

  -- Re-export accessors

  ) where

import Environment.Types




