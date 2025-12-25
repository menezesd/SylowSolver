-- | Shared builders for facts and disjunctions.
-- Centralizes symbol interning, normalization, and key/hash computation.
module Environment.Builders
  ( BuiltFact(..)
  , BuiltDisjunction(..)
  , buildFact
  , buildDisjunction
  ) where

import Core
import ProofMonad
import Environment.Types
import Data.Hashable (hash)
import qualified Data.Set as Set
import qualified Data.List as List

data BuiltFact = BuiltFact
  { bfEntry :: FactEntry
  }

data BuiltDisjunction = BuiltDisjunction
  { bdEntry :: DisjunctionEntry
  , bdSubFacts :: [NewConclusion]
  }

-- Normalize a fact: intern symbols, compute key/hash, attach provenance/depth.
buildFact :: NewConclusion -> Fact -> ProofM BuiltFact
buildFact nc f = do
  fInterned <- internFactSymbols f
  lbl <- newLabelM
  caseDepth <- getsEnv peCaseDepth
  let prov = mkProvenance nc
      entry = FactEntry
        { feFact = fInterned
        , feLabel = lbl
        , feProv = prov
        , feUseful = False
        , feDepth = caseDepth
        , feHash = HashKey (hash (factKey fInterned))
        , feKey = factKey fInterned
        }
  pure (BuiltFact entry)

-- Normalize and build a disjunction: sort/dedup facts and compute hash/key.
buildDisjunction :: NewConclusion -> [Fact] -> ProofM BuiltDisjunction
buildDisjunction nc facts = do
  builtFacts <- mapM (buildFact nc) facts
  let normalizedFacts =
        List.nubBy (\a b -> factKey a == factKey b && factArgs a == factArgs b)
        . List.sortOn (\(Fact n args) -> (n, args))
        $ map (feFact . bfEntry) builtFacts
      prov = mkProvenance nc
      disj = DisjunctionEntry
        { deFacts = normalizedFacts
        , deLabel = DisjId 0
        , deProv = prov
        , deUseful = False
        , deHash = HashKey (hash normalizedFacts)
        }
      subConcs =
        [ NewConclusion (CFact f) [LDisj disjLabel] (Set.singleton (disjLabel, i)) (ncConcThm nc)
        | (i, f) <- zip [0..] normalizedFacts
        , let disjLabel = deLabel disj
        ]
  pure (BuiltDisjunction disj subConcs)

-- Intern all concrete symbols in a fact using the environment's symbol table.
internFactSymbols :: Fact -> ProofM Fact
internFactSymbols (Fact n args) = do
  args' <- mapM internArg args
  pure (Fact n args')
  where
    internArg (Sym symVal) = Sym <$> internSymbolM (symbolName symVal)
    internArg other = pure other
