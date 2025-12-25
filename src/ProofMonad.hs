{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module ProofMonad
  ( ProofM
  , runProofM
  , evalProofM
  , execProofM
  , getEnv
  , putEnv
  , modifyEnv
  , getsEnv
  -- Monadic versions of common operations
  , newLabelM
  , newDisjLabelM
  , generateSymbolM
  , updateFactDBM
  , updateGoalStateM
  , updateGenStateM
  , updateCaseStateM
  ) where

-- Standard library
import Control.Monad.State.Strict
-- Local modules
import Core
import Environment.Types
import Environment.Labels (newDisjunctionLabel, newFactLabel)
import Environment.Symbols (generateNewSymbol)

-- The proof monad is a State monad over ProofEnvironment
newtype ProofM a = ProofM { unProofM :: State ProofEnvironment a }
  deriving (Functor, Applicative, Monad, MonadState ProofEnvironment)

-- Run the proof monad and return both result and final environment
runProofM :: ProofM a -> ProofEnvironment -> (a, ProofEnvironment)
runProofM m = runState (unProofM m)

-- Run and return only the result
evalProofM :: ProofM a -> ProofEnvironment -> a
evalProofM m = evalState (unProofM m)

-- Run and return only the final environment
execProofM :: ProofM a -> ProofEnvironment -> ProofEnvironment
execProofM m = execState (unProofM m)

-- Get the entire environment
getEnv :: ProofM ProofEnvironment
getEnv = get

-- Replace the entire environment
putEnv :: ProofEnvironment -> ProofM ()
putEnv = put

-- Modify the environment with a function
modifyEnv :: (ProofEnvironment -> ProofEnvironment) -> ProofM ()
modifyEnv = modify

-- Get a projection of the environment
getsEnv :: (ProofEnvironment -> a) -> ProofM a
getsEnv = gets

-- Generate a new fact label
newLabelM :: ProofM FactId
newLabelM = state newFactLabel

-- Generate a new disjunction label (or reuse existing)
newDisjLabelM :: DisjunctionEntry -> ProofM DisjId
newDisjLabelM disj = state (\env -> newDisjunctionLabel env disj)

-- Generate a new unique symbol
generateSymbolM :: ProofM String
generateSymbolM = state generateNewSymbol

-- Update sub-structures in a monadic style
updateFactDBM :: (FactDatabase -> FactDatabase) -> ProofM ()
updateFactDBM f = modifyEnv (updateFactDB f)

updateGoalStateM :: (GoalState -> GoalState) -> ProofM ()
updateGoalStateM f = modifyEnv (updateGoalState f)

updateGenStateM :: (GeneratorState -> GeneratorState) -> ProofM ()
updateGenStateM f = modifyEnv (updateGenState f)

updateCaseStateM :: (CaseState -> CaseState) -> ProofM ()
updateCaseStateM f = modifyEnv (updateCaseState f)
