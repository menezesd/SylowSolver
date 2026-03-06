module ProofTrace
  ( ProofStep(..)
  , buildTrace
  -- Accessor functions
  , psLabel
  , psFact
  , psDependencies
  , psDisAncestors
  , psConcThm
  , psUseful
  ) where

import Core
import Env
import Environment.Types (peOrderedFacts, peFactLabels)
import Data.Maybe (mapMaybe)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Set as Set

-- ProofStep now wraps FactEntry directly instead of reconstructing fields
data ProofStep = ProofStep
  { psFactEntry :: FactEntry
  , psSymbols :: SymbolTable
  } deriving (Eq)

-- Accessor functions for backward compatibility
psLabel :: ProofStep -> Label
psLabel = LFact . feLabel . psFactEntry

psFact :: ProofStep -> Fact
psFact = feFact . psFactEntry

psDependencies :: ProofStep -> [Label]
psDependencies = feDependencies . psFactEntry

psDisAncestors :: ProofStep -> [(DisjId, Int)]
psDisAncestors = Set.toList . feDisAncestors . psFactEntry

psConcThm :: ProofStep -> Maybe TheoremName
psConcThm = feConcThm . psFactEntry

psUseful :: ProofStep -> Bool
psUseful = feUseful . psFactEntry

-- | Build a proof trace from the environment.
-- Reverses to get chronological order (fdOrderedFacts is newest-first).
buildTrace :: ProofEnvironment -> [ProofStep]
buildTrace env = mapMaybe toStep (reverse (peOrderedFacts env))
  where
    symTbl = symbolTable env
    labels = peFactLabels env
    toStep lbl = case HashMap.lookup lbl labels of
      Just (LFactEntry fe) -> Just (ProofStep fe symTbl)
      _ -> Nothing

instance Show ProofStep where
  show (ProofStep fe symTbl) =
    labelText (LFact (feLabel fe)) ++ " : " ++ ppFactWithSymbols symTbl (feFact fe)
