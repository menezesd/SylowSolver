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

import Control.Monad.State.Strict
import Environment.Types
import Environment.Accessors
import Environment.Labels (disjunctionKey, disjLabelText)
import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List (intercalate, sort)

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
newLabelM = do
  env <- get
  let lbl = FactId (peCurFactNum env)
  modifyEnv (updateGenState (\gs -> gs { gsCurFactNum = gsCurFactNum gs + 1 }))
  return lbl

-- Generate a new disjunction label (or reuse existing)
newDisjLabelM :: DisjunctionEntry -> ProofM DisjId
newDisjLabelM disj = do
  env <- get
  let key = disjunctionKey disj
  case Map.lookup key (peDisjLabels env) of
    Just existingId -> return existingId
    Nothing -> do
      let newId = DisjId (peCurDisjNum env)
      modifyEnv (updateGenState (\gs -> gs { gsCurDisjNum = gsCurDisjNum gs + 1 }))
      modifyEnv (updateFactDB (\db -> db { fdDisjLabels = Map.insert key newId (fdDisjLabels db) }))
      return newId

-- Generate a new unique symbol
generateSymbolM :: ProofM String
generateSymbolM = do
  env <- get
  let (env', sym) = go (peCurLetter env) (peCurSuffix env) env
  put env'
  return sym
  where
    go curLetter curSuffix env =
      let suffix = if curSuffix == 0 then "" else show curSuffix
          sym = curLetter : suffix
          nextLetter = if curLetter == 'Z' then 'A' else succ curLetter
          nextSuffix = if curLetter == 'Z' then curSuffix + 1 else curSuffix
       in if Set.member sym (peSymbolSet env)
            then go nextLetter nextSuffix env
            else
              ( updateGenState (\gs -> gs
                  { gsCurLetter = nextLetter
                  , gsCurSuffix = nextSuffix
                  , gsSymbolSet = Set.insert sym (gsSymbolSet gs)
                  }) env
              , sym
              )

-- Update sub-structures in a monadic style
updateFactDBM :: (FactDatabase -> FactDatabase) -> ProofM ()
updateFactDBM f = modifyEnv (updateFactDB f)

updateGoalStateM :: (GoalState -> GoalState) -> ProofM ()
updateGoalStateM f = modifyEnv (updateGoalState f)

updateGenStateM :: (GeneratorState -> GeneratorState) -> ProofM ()
updateGenStateM f = modifyEnv (updateGenState f)

updateCaseStateM :: (CaseState -> CaseState) -> ProofM ()
updateCaseStateM f = modifyEnv (updateCaseState f)
