module Environment.Facts
  ( addNewFacts
  , applyThm
  , applyStdThm
  ) where

import Core
import Environment.Types
import Environment.Accessors
import Environment.Labels
import Environment.Goals
import Environment.Variables
import Unification
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

-- Apply a theorem to facts and generate new conclusions
applyThm :: ProofEnvironment -> Thm -> [FactEntry] -> (ProofEnvironment, [FactEntry])
applyThm env thm facts =
  let usedAnc = Set.unions (map feDisAncestors facts)
      usedDict = Map.fromList (Set.toList usedAnc)
      consistent = all (\(d, i) -> Map.lookup d usedDict == Just i) (Set.toList usedAnc)
   in if not consistent
        then (env, [])
        else
          let concs =
                case thm of
                  Std t -> map CFact (applyStdThm t facts)
                  Hyper t -> hyperRule t (map feFact facts)
              deps = map (LFact . feLabel) facts
              nc =
                [ NewConclusion c deps usedAnc (Just (thmName thm))
                | c <- concs
                ]
              (env', nc') = replaceVariables env nc
              (env'', newEntries) = addNewFacts env' nc'
           in (env'', newEntries)

-- Apply a standard theorem via unification
applyStdThm :: Theorem -> [FactEntry] -> [Fact]
applyStdThm thm facts =
  case unifyFacts Map.empty (theoremFacts thm) (map feFact facts) of
    Left _ -> []
    Right mapping -> map (applySubstToFact mapping) (theoremConcs thm)

-- Add new facts and disjunctions to the environment
addNewFacts :: ProofEnvironment -> [NewConclusion] -> (ProofEnvironment, [FactEntry])
addNewFacts env concs =
  let (env', newEntriesReversed) = foldl addOne (env, []) concs
  in (env', reverse newEntriesReversed)
  where
    addOne (acc, addedFactsReversed) nc =
      case ncConclusion nc of
        CFact f ->
          let (acc', entry) = addFact acc nc f
          in (acc', entry : addedFactsReversed)
        CDisj (Disjunction fs) ->
          let (acc', subFactsAddedReversed) = addDisjunction acc nc fs
          in (acc', subFactsAddedReversed ++ addedFactsReversed)

    addFact acc nc f =
      let (acc', lbl) = newFactLabel acc
          symbols' =
            Set.union
              (peSymbolSet acc')
              (Set.fromList (map argText (factArgs f)))
          prov = Provenance
            { provDeps = ncDependencies nc
            , provDisAncestors = ncDisAncestors nc
            , provThm = ncConcThm nc
            }
          entry =
            FactEntry
              { feFact = f
              , feLabel = lbl
              , feProv = prov
              , feUseful = False
              , feDepth = peCaseDepth acc'
              }
          acc'' = updateFactDB (\db -> db
            { fdFactLabels = Map.insert (LFact lbl) (LFactEntry entry) (fdFactLabels db)
            , fdFacts = entry : fdFacts db
            , fdOrderedFacts = LFact lbl : fdOrderedFacts db
            , fdFactIndex = Map.insertWith (++) (factKey f) [entry] (fdFactIndex db)
            }) acc'
          acc''' = updateGenState (\gs -> gs { gsSymbolSet = symbols' }) acc''
          accGoal =
            if factEquals f (peGoal acc''')
              then
                let accG = updateGoalState (\gst -> gst
                      { gsDisCombos = ncDisAncestors nc : gsDisCombos gst }) acc'''
                    accG' = updateUseful (LFact lbl) accG
                 in updateGoalAchieved accG'
              else acc'''
       in (accGoal, entry)

    addDisjunction acc nc fs =
      let prov = Provenance
            { provDeps = ncDependencies nc
            , provDisAncestors = ncDisAncestors nc
            , provThm = ncConcThm nc
            }
          disj =
            DisjunctionEntry
              { deFacts = fs
              , deLabel = DisjId 0
              , deProv = prov
              , deUseful = False
              }
          (acc', lbl) = newDisjunctionLabel acc disj
          disj' = disj {deLabel = lbl}
          acc'' = updateFactDB (\db -> db
            { fdFactLabels = Map.insert (LDisj lbl) (LDisjEntry disj') (fdFactLabels db)
            , fdDisjunctions = disj' : fdDisjunctions db
            , fdOrderedFacts = LDisj lbl : fdOrderedFacts db
            }) acc'
          subConcs =
            [ NewConclusion (CFact f) [LDisj lbl] (Set.insert (lbl, i) (deDisAncestors disj')) (ncConcThm nc)
            | (i, f) <- zip [0 ..] fs
            ]
          (finalAcc, subFactsAddedReversed) = addNewFacts acc'' subConcs
       in (finalAcc, subFactsAddedReversed)
