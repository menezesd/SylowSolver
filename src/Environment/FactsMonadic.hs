module Environment.FactsMonadic
  ( addFactM
  , addNewFactsM
  , addDisjunctionM
  , applyThmM
  ) where

import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Environment.Builders
import Core
import Environment.Types
import Environment.Goals (updateGoalAchieved, updateUseful)
import Environment.Variables
import ProofMonad
import Unification (applyStdThm)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import qualified Data.IntMap.Strict as IntMap

-- Add a single fact in monadic style
addFactM :: NewConclusion -> Fact -> ProofM FactEntry
addFactM nc f = do
  BuiltFact entry <- buildFact nc f
  let lbl = feLabel entry

  -- Update fact database
  updateFactDBM $ \db -> db
    { fdFactLabels = Map.insert (LFact lbl) (LFactEntry entry) (fdFactLabels db)
    , fdFacts = entry : fdFacts db
    , fdOrderedFacts = LFact lbl : fdOrderedFacts db
    , fdFactIndex = IntMap.insertWith (++) (unHashKey (feHash entry)) [entry] (fdFactIndex db)
    }
  updateGenStateM $ \gs -> gs { gsStats = (gsStats gs) { esFacts = esFacts (gsStats gs) + 1 } }

  -- Check if this fact achieves the goal
  goal <- getsEnv peGoal
  when (feFact entry == goal) $ do
    updateGoalStateM $ \gs -> gs { gsDisCombos = ncDisAncestors nc : gsDisCombos gs }
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

  -- Update fact database
  updateFactDBM $ \db -> db
    { fdFactLabels = Map.insert (LDisj lbl) (LDisjEntry disj') (fdFactLabels db)
    , fdDisjunctions = disj' : fdDisjunctions db
    , fdOrderedFacts = LDisj lbl : fdOrderedFacts db
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
  let usedAnc = Set.unions (map feDisAncestors facts)
      usedDict = Map.fromList (Set.toList usedAnc)
      consistent = all (\(d, i) -> Map.lookup d usedDict == Just i) (Set.toList usedAnc)

  if not consistent
    then return []
    else do
      -- Generate conclusions
      let concs = case thm of
            Std t -> map CFact (applyStdThm t facts)
            Hyper t -> fromMaybe [] (hyperRule t (map feFact facts))
          deps = map (LFact . feLabel) facts
          nc = [ NewConclusion c deps usedAnc (Just (thmId thm))
               | c <- concs
               ]

      -- Replace variables and add facts
      env <- getEnv
      let (env', nc') = replaceVariables env nc
      putEnv env'
      addNewFactsM nc'
