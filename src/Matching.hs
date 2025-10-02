-- | Template matching and substitution utilities
module Matching where

import qualified Data.Map.Strict as M
import Types
import Errors

-- Utility functions for argument types
isFixed :: String -> Bool
isFixed ('*':_) = True
isFixed _ = False

isWildcard :: String -> Bool
isWildcard ('?':_) = True
isWildcard _ = False

-- Template matching with error handling
matchTemplate :: [Fact] -> Template -> ProverResult Subst
matchTemplate facts (Template patterns)
  | length facts /= length patterns = 
      Left $ MatchError $ "Fact count mismatch: " ++ show (length facts) ++ " vs " ++ show (length patterns)
  | otherwise = matchFactList M.empty (zip facts patterns)
  where
    matchFactList :: Subst -> [(Fact, Fact)] -> ProverResult Subst
    matchFactList sigma [] = Right sigma
    matchFactList sigma ((fact, pattern) : rest)
      | fName fact /= fName pattern = 
          Left $ MatchError $ "Name mismatch: " ++ fName fact ++ " vs " ++ fName pattern
      | length (fArgs fact) /= length (fArgs pattern) = 
          Left $ MatchError $ "Arity mismatch for " ++ fName fact
      | otherwise = do
          sigma' <- matchArguments sigma (zip (fArgs fact) (fArgs pattern))
          matchFactList sigma' rest

    matchArguments :: Subst -> [(String, String)] -> ProverResult Subst
    matchArguments sigma [] = Right sigma
    matchArguments sigma ((arg, patternArg) : rest)
      | isFixed patternArg = 
          if arg == drop 1 patternArg 
          then matchArguments sigma rest
          else Left $ MatchError $ "Fixed argument mismatch: " ++ arg ++ " vs " ++ patternArg
      | isWildcard patternArg = matchArguments sigma rest -- Skip wildcards
      | otherwise = case M.lookup patternArg sigma of
          Nothing -> matchArguments (M.insert patternArg arg sigma) rest
          Just existingArg 
            | existingArg == arg -> matchArguments sigma rest
            | otherwise -> Left $ SubstitutionError 
                ("Conflicting substitution for " ++ patternArg ++ ": " ++ existingArg ++ " vs " ++ arg) sigma

-- Apply substitution to a fact
substFact :: Subst -> Fact -> Fact
substFact subst fact = fact { fArgs = map substituteArg (fArgs fact) }
  where
    substituteArg x
      | isFixed x = x
      | isWildcard x = x
      | otherwise = M.findWithDefault x x subst