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
matchTemplate :: [Fact] -> TTemplate -> ProverResult Subst
matchTemplate facts (TTemplate patterns)
  | length facts /= length patterns =
      Left $ MatchError $ "Fact count mismatch: " ++ show (length facts) ++ " vs " ++ show (length patterns)
  | otherwise =
      -- Parse incoming facts' args into typed Values (best-effort)
      let parseArg s = case parseValue s of
                         Just v -> v
                         Nothing -> case readInt s of
                                      Just n -> Nat n
                                      Nothing -> Sym s
          parseFact (Fact nm args deps prov) = (nm, map parseArg args, deps, prov)
          typedFacts = map parseFact facts
      in matchTyped M.empty (zip typedFacts patterns)
  where
    -- Match a list of facts against typed patterns, producing a substitution on variables
    -- Subst maps variable names to their concrete string encodings (renderValue)
    matchTyped :: Subst -> [((String,[Value],a,b), TPattern)] -> ProverResult Subst
    matchTyped sigma [] = Right sigma
    matchTyped sigma (((fn, fvs, _, _), TPattern pn pargs):rest)
      | fn /= pn = Left $ MatchError $ "Name mismatch: " ++ fn ++ " vs " ++ pn
      | length fvs /= length pargs = Left $ MatchError $ "Arity mismatch for " ++ fn
      | otherwise = do
          sigma' <- matchArgs sigma (zip fvs pargs)
          matchTyped sigma' rest

    matchArgs :: Subst -> [(Value, ValuePat)] -> ProverResult Subst
    matchArgs sigma [] = Right sigma
    matchArgs sigma ((val, pat):rest) = case pat of
      VWildcard -> matchArgs sigma rest
      VFixed vfixed ->
        if val == vfixed
          then matchArgs sigma rest
          else Left $ MatchError $ "Fixed argument mismatch"
      VVar name -> case M.lookup name sigma of
        Nothing -> matchArgs (M.insert name (renderValue val) sigma) rest
        Just existing ->
          if existing == renderValue val
            then matchArgs sigma rest
            else Left $ SubstitutionError ("Conflicting substitution for " ++ name) sigma

-- Apply substitution to a fact
substFact :: Subst -> Fact -> Fact
substFact subst fact = fact { fArgs = map substituteArg (fArgs fact) }
  where
    substituteArg x
      | isFixed x = x
      | isWildcard x = x
      | otherwise = M.findWithDefault x x subst