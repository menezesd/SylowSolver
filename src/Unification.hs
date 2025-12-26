{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | First-order unification for matching theorem premises to facts.
--
-- This module implements unification between template patterns (from theorem
-- premises) and concrete facts. The key argument types are:
--
--   * 'Sym' \/ 'Num' \/ 'Exact': Must match structurally
--   * 'Var': Binds to any value; repeated occurrences must bind consistently
--   * 'Fresh': Like 'Var' but generates a new symbol when the theorem fires
--
-- Substitutions map variable names to their bound string values.
--
-- == Error Handling Strategy
--
-- This module uses 'Either UnificationError' for explicit error reporting.
-- Errors include:
--
--   * 'NameMismatch': Predicate names don't match
--   * 'ArityMismatch': Different number of arguments
--   * 'StructuralMismatch': Concrete values don't match
--   * 'ConflictingBinding': Variable already bound to different value
--
-- Callers that try multiple unifications (e.g., theorem matching) typically
-- convert errors to empty results, as unification failure is expected when
-- probing potential matches.
--
module Unification
  ( Substitution
  , unSubstitution
  , emptySubstitution
  , nullSubstitution
  , lookupSubst
  , insertSubst
  , substFromList
  , singletonSubst
  , UnificationError(..)
  , unify
  , unifyFact
  , unifyFacts
  , unifyArg
  , applySubstToFact
  , applySubstToArg
  , applyStdThm
  ) where

import Core
import Environment.Types
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- Type-safe wrapper around substitutions (variable name -> argument binding)
newtype Substitution = Substitution { unSubstitution :: Map String Arg }
  deriving stock (Eq, Show)
  deriving newtype (Semigroup, Monoid)

{-# INLINE emptySubstitution #-}
emptySubstitution :: Substitution
emptySubstitution = Substitution Map.empty

{-# INLINE nullSubstitution #-}
nullSubstitution :: Substitution -> Bool
nullSubstitution = Map.null . unSubstitution

{-# INLINE lookupSubst #-}
lookupSubst :: String -> Substitution -> Maybe Arg
lookupSubst name (Substitution subst) = Map.lookup name subst

{-# INLINE insertSubst #-}
insertSubst :: String -> Arg -> Substitution -> Substitution
insertSubst name arg (Substitution subst) = Substitution (Map.insert name arg subst)

{-# INLINE substFromList #-}
substFromList :: [(String, Arg)] -> Substitution
substFromList = Substitution . Map.fromList

{-# INLINE singletonSubst #-}
singletonSubst :: String -> Arg -> Substitution
singletonSubst name arg = Substitution (Map.singleton name arg)

-- Unification errors
data UnificationError
  = NameMismatch PredName PredName
  | ArityMismatch Int Int
  | ExactMismatch Arg Arg -- Changed from String String
  | ConflictingBinding String Arg Arg -- Changed to Arg Arg
  deriving (Eq, Show)

-- Unify a single fact with another fact
{-# INLINE unify #-}
unify :: Fact -> Fact -> Either UnificationError Substitution
unify = unifyFact mempty

-- Unify a fact with a substitution already in place
{-# INLINE unifyFact #-}
unifyFact :: Substitution -> Fact -> Fact -> Either UnificationError Substitution
unifyFact subst (Fact tName tArgs) (Fact fName fArgs)
  | tName /= fName = Left (NameMismatch tName fName)
  | length tArgs /= length fArgs = Left (ArityMismatch (length tArgs) (length fArgs))
  | otherwise = foldl step (Right subst) (zip tArgs fArgs)
  where
    step :: Either UnificationError Substitution -> (Arg, Arg) -> Either UnificationError Substitution
    step (Left err) _ = Left err
    step (Right m) (tArg, fArg) = unifyArg m tArg fArg

-- Unify multiple facts in sequence
{-# INLINE unifyFacts #-}
unifyFacts :: Substitution -> [Fact] -> [Fact] -> Either UnificationError Substitution
unifyFacts subst [] [] = Right subst
unifyFacts subst (t : ts) (f : fs) = do
  subst' <- unifyFact subst t f
  unifyFacts subst' ts fs
unifyFacts _ ts fs = Left (ArityMismatch (length ts) (length fs))

-- Unify a single argument with a substitution already in place
-- Optimized to avoid argText allocations in hot paths
{-# INLINE unifyArg #-}
unifyArg :: Substitution -> Arg -> Arg -> Either UnificationError Substitution
unifyArg subst tArg fArg =
  case (tArg, fArg) of
    -- Exact matches: structural comparison
    (Exact n1, Exact n2) | n1 == n2 -> Right subst
    (Exact n1, Sym sym2) | n1 == symbolName sym2 -> Right subst
    (Exact n, Num i) | n == show i -> Right subst
    (Exact _, _) -> Left (ExactMismatch tArg fArg)

    -- Sym matches: structural comparison
    (Sym n1, Sym n2) | n1 == n2 -> Right subst
    (Sym (Symbol _ n1), Exact n2) | n1 == n2 -> Right subst
    (Sym symVal, Num i) | symbolName symVal == show i -> Right subst
    (Sym _, _) -> Left (ExactMismatch tArg fArg)

    -- Num matches: structural comparison
    (Num i1, Num i2) | i1 == i2 -> Right subst
    (Num i, Sym symVal) | show i == symbolName symVal -> Right subst
    (Num i, Exact n) | show i == n -> Right subst
    (Num _, _) -> Left (ExactMismatch tArg fArg)

    -- Var: binds to anything (need string representation for substitution)
    (Var name, _) ->
      case lookupSubst name subst of
        Nothing -> Right (insertSubst name fArg subst)
        Just v ->
          if v == fArg
                then Right subst
                else Left (ConflictingBinding name v fArg)

    -- Fresh: binds to anything (need string representation for substitution)
    (Fresh name, _) ->
      case lookupSubst name subst of
        Nothing -> Right (insertSubst name fArg subst)
        Just v ->
          if v == fArg
                then Right subst
                else Left (ConflictingBinding name v fArg)

-- Apply standard theorem via unification
-- Takes premises and conclusions directly (GADT-friendly)
applyStdThm :: [Fact] -> [Fact] -> [FactEntry] -> [Fact]
applyStdThm premises conclusions facts =
  case unifyFacts mempty premises (map feFact facts) of
    Left _ -> []
    Right mapping -> map (applySubstToFact mapping) conclusions

-- Apply substitution to a fact
{-# INLINE applySubstToFact #-}
applySubstToFact :: Substitution -> Fact -> Fact
applySubstToFact subst (Fact name args) =
  Fact name (map (applySubstToArg subst) args)

-- Apply substitution to an argument
{-# INLINE applySubstToArg #-}
applySubstToArg :: Substitution -> Arg -> Arg
applySubstToArg subst arg =
  case arg of
    Var name ->
      case lookupSubst name subst of
        Just boundArg -> boundArg
        Nothing -> arg
    Exact name ->
      case lookupSubst name subst of
        Just boundArg -> boundArg
        Nothing -> Exact name -- If not bound, it remains an Exact
    Fresh name ->
      case lookupSubst name subst of
        Just boundArg -> boundArg
        Nothing -> arg
    Sym _ -> arg
    Num _ -> arg
