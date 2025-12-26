{-# LANGUAGE RecordWildCards #-}

-- | Shared builders for facts and disjunctions.
-- Centralizes symbol interning, normalization, and key/hash computation.
module Environment.Builders
  ( BuiltFact(..)
  , BuiltDisjunction(..)
  , buildFact
  , buildDisjunction
  , inferDisjMeta
  ) where

import Core
import ProofMonad
import Environment.Types
import Data.Hashable (hash)
import Data.List (transpose)
import Data.Maybe (listToMaybe)
import qualified Data.Set as Set

data BuiltFact = BuiltFact
  { bfEntry :: FactEntry
  }

data BuiltDisjunction = BuiltDisjunction
  { bdEntry :: DisjunctionEntry
  , bdSubFacts :: [NewConclusion]
  }

-- Normalize a fact: intern symbols, compute hash, attach provenance/depth.
{-# INLINE buildFact #-}
buildFact :: NewConclusion -> Fact -> ProofM BuiltFact
buildFact nc f = do
  feFact <- internFactSymbols f
  feLabel <- newLabelM
  feDepth <- getsEnv peCaseDepth
  let feProv = mkProvenance nc
      feUseful = False
      feHash = HashKey (hash feFact)
  pure $ BuiltFact FactEntry {..}

-- Normalize and build a disjunction: sort/dedup facts and compute hash/key.
-- Uses Set for O(n log n) dedup+sort instead of O(n²) nubBy
buildDisjunction :: NewConclusion -> [Fact] -> ProofM BuiltDisjunction
buildDisjunction nc facts = do
  builtFacts <- mapM (buildFact nc) facts
  -- Set.fromList deduplicates and sorts by Ord instance (which orders by (name, args))
  let deFacts = Set.toAscList $ Set.fromList $ map (feFact . bfEntry) builtFacts
      deProv = mkProvenance nc
      deLabel = DisjId 0
      deUseful = False
      deHash = HashKey (hash deFacts)
      disj = DisjunctionEntry {..}
      subConcs =
        [ NewConclusion (CFact f) [LDisj disjLabel] (Set.singleton (disjLabel, i)) (ncConcThm nc)
        | (i, f) <- zip [0..] deFacts
        , let disjLabel = deLabel
        ]
  pure (BuiltDisjunction disj subConcs)

-- Intern all concrete symbols in a fact using the environment's symbol table.
{-# INLINE internFactSymbols #-}
internFactSymbols :: Fact -> ProofM Fact
internFactSymbols (Fact n args) = do
  args' <- mapM internArg args
  pure (Fact n args')
  where
    internArg (Sym symVal) = Sym <$> internSymbolM (symbolName symVal)
    internArg other = pure other

-- | Infer metadata for a disjunction from its facts.
-- Determines the variable name and branch values by analyzing the facts.
inferDisjMeta :: [Fact] -> DisjMeta
inferDisjMeta [] = DisjMeta "?" PFalse []
inferDisjMeta facts@(Fact predName args : _) =
  let -- Find which argument position differs across facts
      allArgs = map factArgs facts
      transposed = transpose allArgs

      -- Find the first argument position that varies
      varyingIdx = findVaryingIndex transposed

      -- Generate variable name based on predicate
      varName = mkVarName predName varyingIdx args

      -- Extract branch values (the varying argument from each fact)
      branchVals = case varyingIdx of
        Just idx -> map (\f -> safeArgAt (factArgs f) idx) facts
        Nothing -> map (const "?") facts

      safeArgAt :: [Arg] -> Int -> String
      safeArgAt as i = case drop i as of
        (a:_) -> ppArg a
        [] -> "?"

   in DisjMeta varName predName branchVals

-- Find the index of the first argument that varies across facts
findVaryingIndex :: [[Arg]] -> Maybe Int
findVaryingIndex argLists =
  listToMaybe [i | (i, args) <- zip [0..] argLists, not (allSame args)]
  where
    allSame [] = True
    allSame (x:xs) = all (== x) xs

-- Generate a readable variable name based on the predicate
mkVarName :: PredName -> Maybe Int -> [Arg] -> String
mkVarName PNumSylow _ args =
  -- num_sylow(p, G, n) -> "n_p" where p is the first argument
  case args of
    (p : _) -> "n" ++ subscript (ppArg p)
    _ -> "n"
mkVarName POrder _ _ = "|G|"
mkVarName PIndex _ _ = "index"
mkVarName pn _ _ = predNameText pn

-- Convert a string to subscript (simple version)
subscript :: String -> String
subscript s = case s of
  "2" -> "₂"
  "3" -> "₃"
  "5" -> "₅"
  "7" -> "₇"
  "11" -> "₁₁"
  "13" -> "₁₃"
  _ -> "_" ++ s
