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
module Unification
  ( Substitution
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

-- Type alias for substitutions
type Substitution = Map String Arg

-- Unification errors
data UnificationError
  = NameMismatch String String
  | ArityMismatch Int Int
  | ExactMismatch Arg Arg -- Changed from String String
  | ConflictingBinding String Arg Arg -- Changed to Arg Arg
  deriving (Eq, Show)

-- Unify a single fact with another fact
unify :: Fact -> Fact -> Either UnificationError Substitution
unify = unifyFact Map.empty

-- Unify a fact with a substitution already in place
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
    (Exact n1, Sym n2) | n1 == n2 -> Right subst
    (Exact n, Num i) | n == show i -> Right subst
    (Exact n, _) -> Left (ExactMismatch tArg fArg)

    -- Sym matches: structural comparison
    (Sym n1, Sym n2) | n1 == n2 -> Right subst
    (Sym n1, Exact n2) | n1 == n2 -> Right subst
    (Sym n, Num i) | n == show i -> Right subst
    (Sym n, _) -> Left (ExactMismatch tArg fArg)

    -- Num matches: structural comparison
    (Num i1, Num i2) | i1 == i2 -> Right subst
    (Num i, Sym n) | show i == n -> Right subst
    (Num i, Exact n) | show i == n -> Right subst
    (Num i, _) -> Left (ExactMismatch tArg fArg)

    -- Var: binds to anything (need string representation for substitution)
    (Var name, _) ->
      case Map.lookup name subst of
        Nothing -> Right (Map.insert name fArg subst)
        Just v ->
          if v == fArg
                then Right subst
                else Left (ConflictingBinding name v fArg)

    -- Fresh: binds to anything (need string representation for substitution)
    (Fresh name, _) ->
      case Map.lookup name subst of
        Nothing -> Right (Map.insert name fArg subst)
        Just v ->
          if v == fArg
                then Right subst
                else Left (ConflictingBinding name v fArg)

-- Apply standard theorem via unification
applyStdThm :: Theorem -> [FactEntry] -> [Fact]
applyStdThm thm facts =
  case unifyFacts Map.empty (theoremFacts thm) (map feFact facts) of
    Left _ -> []
    Right mapping -> map (applySubstToFact mapping) (theoremConcs thm)

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
      case Map.lookup name subst of
        Just boundArg -> boundArg
        Nothing -> arg
    Exact name ->
      case Map.lookup name subst of
        Just boundArg -> boundArg
        Nothing -> Exact name -- If not bound, it remains an Exact
    Fresh name ->
      case Map.lookup name subst of
        Just boundArg -> boundArg
        Nothing -> arg
    Sym _ -> arg
    Num _ -> arg

