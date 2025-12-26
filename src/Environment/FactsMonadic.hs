module Environment.FactsMonadic
  ( addFactM
  , addNewFactsM
  , addDisjunctionM
  , applyThmM
  ) where

import Control.Monad (when)
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Environment.Builders (BuiltFact(..), BuiltDisjunction(..), buildFact, buildDisjunction, inferDisjMeta)
import Core
import Environment.Types
import Environment.Goals (updateGoalAchieved, updateUseful)
import Environment.Variables (replaceVariables, hasFreshVars)
import ProofMonad
import Unification (applyStdThm)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap

-- Add a single fact in monadic style, with deduplication
addFactM :: NewConclusion -> Fact -> ProofM FactEntry
addFactM nc f = do
  BuiltFact entry <- buildFact nc f

  -- Check for existing duplicate (same fact content AND same case context)
  let hashKey = unHashKey (feHash entry)
      caseCtx = ncDisAncestors nc
  factIndex <- getsEnv peFactIndex
  let existingFacts = IntMap.findWithDefault [] hashKey factIndex
      isDuplicate existing = feFact existing == feFact entry
                          && feDisAncestors existing == caseCtx

  case filter isDuplicate existingFacts of
    (existing:_) -> return existing  -- Return existing fact, don't add duplicate
    [] -> do
      -- No duplicate found, add the new fact
      let lbl = feLabel entry
      updateFactDBM $ \db -> db
        { fdFactLabels = HashMap.insert (LFact lbl) (LFactEntry entry) (fdFactLabels db)
        , fdFacts = entry : fdFacts db
        , fdOrderedFacts = LFact lbl : fdOrderedFacts db
        , fdFactIndex = IntMap.insertWith (++) hashKey [entry] (fdFactIndex db)
        }
      updateGenStateM $ \gs -> gs { gsStats = (gsStats gs) { esFacts = esFacts (gsStats gs) + 1 } }

      -- Check if this fact achieves the goal
      goal <- getsEnv peGoal
      when (feFact entry == goal) $ do
        updateGoalStateM $ \gs -> gs { gsDisCombos = caseCtx : gsDisCombos gs }
        modifyEnv (updateUseful (LFact lbl))
        modifyEnv updateGoalAchieved

      return entry

-- Add a disjunction in monadic style
addDisjunctionM :: NewConclusion -> [Fact] -> ProofM [FactEntry]
addDisjunctionM nc fs = do
  BuiltDisjunction disjEntry subConcs <- buildDisjunction nc fs

  -- Get or create label
  lbl <- newDisjLabelM disjEntry
  let disj' = disjEntry { deLabel = lbl }
      DisjId lblInt = lbl
      meta = inferDisjMeta (deFacts disj')

  -- Update fact database
  updateFactDBM $ \db -> db
    { fdFactLabels = HashMap.insert (LDisj lbl) (LDisjEntry disj') (fdFactLabels db)
    , fdDisjunctions = disj' : fdDisjunctions db
    , fdOrderedFacts = LDisj lbl : fdOrderedFacts db
    , fdDisjMeta = IntMap.insert lblInt meta (fdDisjMeta db)
    }
  updateGenStateM $ \gs -> gs { gsStats = (gsStats gs) { esDisjunctions = esDisjunctions (gsStats gs) + 1 } }

  -- Add sub-facts from disjunction
  let adjustedSubConcs =
        [ conc { ncDependencies = [LDisj lbl]
               , ncDisAncestors = Set.insert (lbl, i) (ncDisAncestors conc)
               }
        | (i, conc) <- zip [0..] subConcs
        ]
  addNewFactsM adjustedSubConcs

-- Add multiple new conclusions in monadic style
addNewFactsM :: [NewConclusion] -> ProofM [FactEntry]
addNewFactsM concs = concat <$> mapM addOneM concs
  where
    addOneM nc = case ncConclusion nc of
      CFact f -> (:[]) <$> addFactM nc f
      CDisj (Disjunction fs) -> addDisjunctionM nc fs

-- Apply a theorem in monadic style
applyThmM :: Thm -> [FactEntry] -> ProofM [FactEntry]
applyThmM thm facts = do
  -- Check disjunction ancestor consistency
  let usedAnc = foldl' Set.union Set.empty (map feDisAncestors facts)
      usedDict = Map.fromList (Set.toList usedAnc)
      consistent = all (\(d, i) -> Map.lookup d usedDict == Just i) (Set.toList usedAnc)

  if not consistent
    then return []
    else do
      -- Generate conclusions
      let concs = case thm of
            Std _ prems conc -> map CFact (applyStdThm prems conc facts)
            Hyper _ _ rule -> fromMaybe [] (rule (map feFact facts))
          deps = map (LFact . feLabel) facts
          nc = [ NewConclusion c deps usedAnc (Just (thmId thm))
               | c <- concs
               ]

      -- Replace Fresh variables only if present (optimization)
      if hasFreshVars nc
        then do
          env <- getEnv
          let (env', nc') = replaceVariables env nc
          putEnv env'
          addNewFactsM nc'
        else addNewFactsM nc
