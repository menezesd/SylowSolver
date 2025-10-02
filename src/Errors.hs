-- | Error types for the Sylow solver
{-# LANGUAGE DeriveGeneric #-}
module Errors where

import GHC.Generics (Generic)
import Types

-- | Comprehensive error type for the prover
data ProverError
  = ParseError String                    -- ^ Error parsing input
  | MatchError String                    -- ^ Template matching failed  
  | SubstitutionError String Subst       -- ^ Invalid substitution
  | TheoremApplicationError String [Fact] -- ^ Theorem application failed
  | EnvironmentError String             -- ^ Environment inconsistency
  | TimeoutError Int                     -- ^ Proof search timed out
  | ResourceLimitError String           -- ^ Hit resource limits
  | LogicError String                   -- ^ Internal logic error
  deriving (Eq, Show, Generic)

-- | Result type for prover operations
type ProverResult a = Either ProverError a

-- | Safe parsing functions
safeRead :: Read a => String -> ProverResult a
safeRead s = case reads s of
  [(x, "")] -> Right x
  _ -> Left $ ParseError $ "Cannot parse: " ++ s

-- | Safe head function
safeHead :: String -> [a] -> ProverResult a
safeHead _ (x:_) = Right x
safeHead msg [] = Left $ LogicError $ "Empty list: " ++ msg

-- | Safe lookup with better error messages
safeLookup :: (Show k, Eq k) => k -> [(k, v)] -> ProverResult v
safeLookup key assocs = case lookup key assocs of
  Just v -> Right v
  Nothing -> Left $ LogicError $ "Key not found: " ++ show key

-- | Convert Maybe to ProverResult with custom error
maybeToResult :: String -> Maybe a -> ProverResult a
maybeToResult msg Nothing = Left $ LogicError msg
maybeToResult _ (Just x) = Right x

-- | Pretty print errors
prettyError :: ProverError -> String
prettyError (ParseError msg) = "Parse Error: " ++ msg
prettyError (MatchError msg) = "Matching Error: " ++ msg
prettyError (SubstitutionError msg subst) = 
  "Substitution Error: " ++ msg ++ " with substitution " ++ show subst
prettyError (TheoremApplicationError thmName facts) = 
  "Failed to apply theorem " ++ thmName ++ " to facts: " ++ show facts
prettyError (EnvironmentError msg) = "Environment Error: " ++ msg
prettyError (TimeoutError rounds) = 
  "Proof search timed out after " ++ show rounds ++ " rounds"
prettyError (ResourceLimitError msg) = "Resource Limit: " ++ msg
prettyError (LogicError msg) = "Internal Logic Error: " ++ msg