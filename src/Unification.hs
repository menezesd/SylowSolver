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
  ) where

import Core
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- Type alias for substitutions
type Substitution = Map String String

-- Unification errors
data UnificationError
  = NameMismatch String String
  | ArityMismatch Int Int
  | ExactMismatch String String
  | ConflictingBinding String String String
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
    (Exact n, Num i) ->
      -- Only stringify when needed for error message
      let nText = argText (Num i)
       in if n == nText then Right subst
          else Left (ExactMismatch n nText)
    (Exact n, _) -> Left (ExactMismatch n (argText fArg))

    -- Sym matches: structural comparison
    (Sym n1, Sym n2) | n1 == n2 -> Right subst
    (Sym n1, Exact n2) | n1 == n2 -> Right subst
    (Sym n, Num i) ->
      let nText = argText (Num i)
       in if n == nText then Right subst
          else Left (ExactMismatch n nText)
    (Sym n, _) -> Left (ExactMismatch n (argText fArg))

    -- Num matches: structural comparison
    (Num i1, Num i2) | i1 == i2 -> Right subst
    (Num i, Sym n) ->
      let iText = argText (Num i)
       in if iText == n then Right subst
          else Left (ExactMismatch iText n)
    (Num i, Exact n) ->
      let iText = argText (Num i)
       in if iText == n then Right subst
          else Left (ExactMismatch iText n)
    (Num i, _) -> Left (ExactMismatch (argText (Num i)) (argText fArg))

    -- Var: binds to anything (need string representation for substitution)
    (Var name, _) ->
      case Map.lookup name subst of
        Nothing -> Right (Map.insert name (argText fArg) subst)
        Just v ->
          let fText = argText fArg
           in if v == fText
                then Right subst
                else Left (ConflictingBinding name v fText)

    -- Fresh: binds to anything (need string representation for substitution)
    (Fresh name, _) ->
      case Map.lookup name subst of
        Nothing -> Right (Map.insert name (argText fArg) subst)
        Just v ->
          let fText = argText fArg
           in if v == fText
                then Right subst
                else Left (ConflictingBinding name v fText)

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
        Just symName -> Sym symName
        Nothing -> arg
    Exact name ->
      case Map.lookup name subst of
        Just symName -> Sym symName
        Nothing -> Sym name
    Fresh name ->
      case Map.lookup name subst of
        Just symName -> Sym symName
        Nothing -> arg
    Sym _ -> arg
    Num _ -> arg  -- Numeric arguments are not substituted

