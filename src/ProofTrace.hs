module ProofTrace
  ( ProofStep(..)
  , buildTrace
  , labelText
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
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- ProofStep now wraps FactEntry directly instead of reconstructing fields
data ProofStep = ProofStep
  { psFactEntry :: FactEntry
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

psConcThm :: ProofStep -> Maybe String
psConcThm = feConcThm . psFactEntry

psUseful :: ProofStep -> Bool
psUseful = feUseful . psFactEntry

buildTrace :: ProofEnvironment -> [ProofStep]
buildTrace env = mapMaybeStep (reverse (peOrderedFacts env))
  -- Reverse to get chronological order (fdOrderedFacts is newest-first)
  where
    mapMaybeStep [] = []
    mapMaybeStep (lbl : rest) =
      case Map.lookup lbl (peFactLabels env) of
        Just (LFactEntry fe) -> ProofStep fe : mapMaybeStep rest
        _ -> mapMaybeStep rest

labelText :: Label -> String
labelText lbl =
  case lbl of
    LFact (FactId n) -> "F" ++ show n
    LDisj (DisjId n) -> "D" ++ show n

instance Show ProofStep where
  show (ProofStep fe) =
    labelText (LFact (feLabel fe)) ++ " : " ++ ppFact (feFact fe)
