module ProofTrace
  ( ProofStep(..)
  , buildTrace
  , labelText
  ) where

import Core
import Env
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data ProofStep = ProofStep
  { psLabel :: Label
  , psFact :: Fact
  , psDependencies :: [Label]
  , psDisAncestors :: [(DisjId, Int)]
  , psConcThm :: Maybe String
  , psUseful :: Bool
  } deriving (Eq, Show)

buildTrace :: ProofEnvironment -> [ProofStep]
buildTrace env = mapMaybeStep (peOrderedFacts env)
  where
    mapMaybeStep [] = []
    mapMaybeStep (lbl : rest) =
      case Map.lookup lbl (peFactLabels env) of
        Just (LFactEntry fe) ->
          let step =
                ProofStep
                  { psLabel = lbl
                  , psFact = feFact fe
                  , psDependencies = feDependencies fe
                  , psDisAncestors = Set.toList (feDisAncestors fe)
                  , psConcThm = feConcThm fe
                  , psUseful = feUseful fe
                  }
           in step : mapMaybeStep rest
        _ -> mapMaybeStep rest

labelText :: Label -> String
labelText lbl =
  case lbl of
    LFact (FactId n) -> "F" ++ show n
    LDisj (DisjId n) -> "D" ++ show n
