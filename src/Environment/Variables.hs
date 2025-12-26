module Environment.Variables
  ( replaceVariables
  , replaceVariablesM
  , hasFreshVars
  ) where

import Core
import Environment.Types
import ProofMonad
import Control.Monad (foldM)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map

-- Monadic version using ProofM for cleaner state threading
replaceVariablesM :: [NewConclusion] -> ProofM [NewConclusion]
replaceVariablesM concs = do
  subst <- buildSubstM concs
  return $ map (applySubstToConc subst) concs
  where
    buildSubstM :: [NewConclusion] -> ProofM (Map String Symbol)
    buildSubstM = foldM collectFreshVars Map.empty

    collectFreshVars :: Map String Symbol -> NewConclusion -> ProofM (Map String Symbol)
    collectFreshVars subst nc =
      foldM processFactForFresh subst (conclusionFacts (ncConclusion nc))

    processFactForFresh :: Map String Symbol -> Fact -> ProofM (Map String Symbol)
    processFactForFresh subst (Fact _ args) =
      foldM processArgForFresh subst args

    processArgForFresh :: Map String Symbol -> Arg -> ProofM (Map String Symbol)
    processArgForFresh subst (Fresh name)
      | Map.member name subst = return subst
      | otherwise = do
          symName <- generateSymbolM
          return (Map.insert name symName subst)
    processArgForFresh subst _ = return subst

    applySubstToConc :: Map String Symbol -> NewConclusion -> NewConclusion
    applySubstToConc subst nc =
      nc { ncConclusion = applySubstToConclusion subst (ncConclusion nc) }

    applySubstToConclusion :: Map String Symbol -> Conclusion -> Conclusion
    applySubstToConclusion subst (CFact f) = CFact (applySubstToFact subst f)
    applySubstToConclusion subst (CDisj (Disjunction fs)) =
      CDisj (Disjunction (map (applySubstToFact subst) fs))

    applySubstToFact :: Map String Symbol -> Fact -> Fact
    applySubstToFact subst f =
      f { factArgs = map (applySubstToArg subst) (factArgs f) }

    applySubstToArg :: Map String Symbol -> Arg -> Arg
    applySubstToArg subst (Fresh name) =
      case Map.lookup name subst of
        Just symName -> Sym symName
        Nothing -> Fresh name
    applySubstToArg _ arg = arg

-- Pure version (backward compatibility wrapper)
replaceVariables :: ProofEnvironment -> [NewConclusion] -> (ProofEnvironment, [NewConclusion])
replaceVariables env concs =
  let (concs', env') = runProofM (replaceVariablesM concs) env
   in (env', concs')

-- | Check if any conclusions contain Fresh variables
-- Used to skip replaceVariables when not needed
hasFreshVars :: [NewConclusion] -> Bool
hasFreshVars = any hasFreshInConc
  where
    hasFreshInConc nc = any hasFreshInFact (conclusionFacts (ncConclusion nc))

    hasFreshInFact (Fact _ args) = any isFresh args

    isFresh (Fresh _) = True
    isFresh _ = False
