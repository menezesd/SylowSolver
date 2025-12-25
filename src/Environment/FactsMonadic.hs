module Environment.FactsMonadic
  ( addFactM
  , addNewFactsM
  , addDisjunctionM
  , applyThmM
  ) where

import Control.Monad (when)
import Data.Maybe (fromMaybe)
import Core
import Environment.Types
import Environment.Goals (updateGoalAchieved, updateUseful)
import Environment.Variables
import ProofMonad
import Unification (applyStdThm)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Add a single fact in monadic style
addFactM :: NewConclusion -> Fact -> ProofM FactEntry
addFactM nc f = do
  lbl <- newLabelM

  -- Collect symbols
  let symbols' = Set.fromList (map argText (factArgs f))
  updateGenStateM (\gs -> gs { gsSymbolSet = Set.union (gsSymbolSet gs) symbols' })

  -- Create entry
  caseDepth <- getsEnv peCaseDepth
  let prov = mkProvenance nc
      entry = FactEntry
        { feFact = f
        , feLabel = lbl
        , feProv = prov
        , feUseful = False
        , feDepth = caseDepth
        }

  -- Update fact database
  updateFactDBM $ \db -> db
    { fdFactLabels = Map.insert (LFact lbl) (LFactEntry entry) (fdFactLabels db)
    , fdFacts = entry : fdFacts db
    , fdOrderedFacts = LFact lbl : fdOrderedFacts db
    , fdFactIndex = Map.insertWith (++) (factKey f) [entry] (fdFactIndex db)
    }

  -- Check if this fact achieves the goal
  goal <- getsEnv peGoal
  when (f == goal) $ do
    updateGoalStateM $ \gs -> gs { gsDisCombos = ncDisAncestors nc : gsDisCombos gs }
    modifyEnv (updateUseful (LFact lbl))
    modifyEnv updateGoalAchieved

  return entry

-- Add a disjunction in monadic style
addDisjunctionM :: NewConclusion -> [Fact] -> ProofM [FactEntry]
addDisjunctionM nc fs = do
  -- Create disjunction entry
  let prov = mkProvenance nc
      disj = DisjunctionEntry
        { deFacts = fs
        , deLabel = DisjId 0  -- Placeholder
        , deProv = prov
        , deUseful = False
        }

  -- Get or create label
  lbl <- newDisjLabelM disj
  let disj' = disj { deLabel = lbl }

  -- Update fact database
  updateFactDBM $ \db -> db
    { fdFactLabels = Map.insert (LDisj lbl) (LDisjEntry disj') (fdFactLabels db)
    , fdDisjunctions = disj' : fdDisjunctions db
    , fdOrderedFacts = LDisj lbl : fdOrderedFacts db
    }

  -- Add sub-facts from disjunction
  let subConcs =
        [ NewConclusion (CFact f) [LDisj lbl] (Set.insert (lbl, i) (deDisAncestors disj')) (ncConcThm nc)
        | (i, f) <- zip [0..] fs
        ]
  addNewFactsM subConcs

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
          nc = [ NewConclusion c deps usedAnc (Just (thmName thm))
               | c <- concs
               ]

      -- Replace variables and add facts
      env <- getEnv
      let (env', nc') = replaceVariables env nc
      putEnv env'
      addNewFactsM nc'

