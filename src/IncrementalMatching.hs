-- | Incremental theorem matching for efficient forward chaining.
--
-- When a new fact is added, this module efficiently finds all theorems
-- that could potentially fire by using a pre-built trigger index. Each
-- theorem premise is indexed by its 'FactKey', allowing O(1) lookup of
-- candidate theorems when a new fact arrives.
--
-- The matching process:
--
--   1. Look up theorems triggered by the new fact's key
--   2. For each trigger, try to complete the match by finding facts
--      for the remaining premises
--   3. Return all complete matches as (theorem, matched-facts) pairs
--
module IncrementalMatching
  ( -- * ProofEnvironment-based matching (convenience wrappers)
    findTriggeredMatches
  , matchFactsToTemplate
  , matchPremises
  , matchPremisesWithSubst
    -- * Pure matching on fact index (for profiling/testing)
  , FactIndex
  , findTriggeredMatchesPure
  , matchFactsToTemplatePure
  , matchPremisesPure
  , matchPremisesWithSubstPure
  ) where

import Core
import Data.Foldable (toList)
import Data.List (foldl')
import Data.Hashable (hash)
import Data.IntMap.Strict (IntMap)
import Data.Sequence (Seq, (|>))
import Environment.Types (TriggerIndex, peFactIndex)
import qualified Data.HashMap.Strict as HashMap
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Sequence as Seq
import Env
import Unification

-- | Type alias for the fact index used in matching
type FactIndex = IntMap [FactEntry]

-- | Type alias for fact sequences (used in incremental matching)
type FactSeq = Seq FactEntry

------------------------------------------------------------------------
-- Pure matching functions (for profiling and deterministic tests)
------------------------------------------------------------------------

-- | Pure version: find all theorems triggered by a new fact
findTriggeredMatchesPure :: FactIndex -> FactEntry -> TriggerIndex -> [(Thm, [FactEntry])]
findTriggeredMatchesPure factIdx newFact triggerIndex =
  let key = factKey (feFact newFact)
      triggers = HashMap.lookupDefault [] key triggerIndex
      tryTrigger trigger =
        let premises = ttPremises trigger
            triggerIdx = ttPremiseIndex trigger
            thm = ttTheorem trigger
            matchResults = matchNewFactAtPositionPure factIdx newFact premises triggerIdx
         in [(thm, match) | match <- matchResults]
   in concatMap tryTrigger triggers

-- | Pure helper: match premises with a specific fact at a given position
matchNewFactAtPositionPure :: FactIndex -> FactEntry -> [Fact] -> Int -> [[FactEntry]]
matchNewFactAtPositionPure factIdx newFact premises targetIdx
  | targetIdx < 0 || targetIdx >= length premises = []
  | otherwise =
      let (beforePremises, targetAndAfter) = splitAt targetIdx premises
       in case targetAndAfter of
            [] -> []
            (targetPremise : afterPremises) ->
              let fact = feFact newFact
               in case unifyFact mempty targetPremise fact of
                    Left _ -> []
                    Right subst ->
                      [ toList fullFacts
                      | (substBefore, beforeFacts) <- matchPremisesWithSubstSeq factIdx subst Seq.empty beforePremises
                      , (_substAfter, fullFacts) <- matchPremisesWithSubstSeq factIdx substBefore (beforeFacts |> newFact) afterPremises
                      ]

-- | Pure version: match a template fact against indexed facts
{-# INLINE matchFactsToTemplatePure #-}
matchFactsToTemplatePure :: FactIndex -> Fact -> Substitution -> [(FactEntry, Substitution)]
matchFactsToTemplatePure factIdx template initMap =
  let templateKey = factKey template
      candidateFacts = IntMap.findWithDefault [] (hash template) factIdx
   in [ (factEntry, matchMap)
      | factEntry <- candidateFacts
      , factKey (feFact factEntry) == templateKey
      , Right matchMap <- [unifyFact initMap template (feFact factEntry)]
      ]

-- | Internal Seq-based matching for O(1) snoc
{-# INLINE matchPremisesWithSubstSeq #-}
matchPremisesWithSubstSeq :: FactIndex -> Substitution -> FactSeq -> [Fact] -> [(Substitution, FactSeq)]
matchPremisesWithSubstSeq factIdx initSubst seedFacts templates =
  foldl' step [(initSubst, seedFacts)] templates
  where
    step acc template =
      [ (subst', facts |> factEntry)
      | (subst, facts) <- acc
      , (factEntry, subst') <- matchFactsToTemplatePure factIdx template subst
      ]

-- | Pure version: match a sequence of premises
{-# INLINE matchPremisesWithSubstPure #-}
matchPremisesWithSubstPure :: FactIndex -> Substitution -> [FactEntry] -> [Fact] -> [(Substitution, [FactEntry])]
matchPremisesWithSubstPure factIdx initSubst seedFacts templates =
  [ (subst, toList facts)
  | (subst, facts) <- matchPremisesWithSubstSeq factIdx initSubst (Seq.fromList seedFacts) templates
  ]

-- | Pure version: convenience wrapper without final substitution
{-# INLINE matchPremisesPure #-}
matchPremisesPure :: FactIndex -> [Fact] -> [[FactEntry]]
matchPremisesPure factIdx templates =
  [ facts
  | (_subst, facts) <- matchPremisesWithSubstPure factIdx mempty [] templates
  ]

------------------------------------------------------------------------
-- ProofEnvironment-based wrappers (convenience)
------------------------------------------------------------------------

-- | Find all theorems triggered by a new fact (convenience wrapper)
findTriggeredMatches :: ProofEnvironment -> FactEntry -> TriggerIndex -> [(Thm, [FactEntry])]
findTriggeredMatches env = findTriggeredMatchesPure (peFactIndex env)

-- | Match a template fact against existing facts (convenience wrapper)
{-# INLINE matchFactsToTemplate #-}
matchFactsToTemplate :: Fact -> ProofEnvironment -> Substitution -> [(FactEntry, Substitution)]
matchFactsToTemplate template env = matchFactsToTemplatePure (peFactIndex env) template

-- | Match premises with substitution (convenience wrapper)
{-# INLINE matchPremisesWithSubst #-}
matchPremisesWithSubst :: ProofEnvironment -> Substitution -> [FactEntry] -> [Fact] -> [(Substitution, [FactEntry])]
matchPremisesWithSubst env = matchPremisesWithSubstPure (peFactIndex env)

-- | Match premises (convenience wrapper)
{-# INLINE matchPremises #-}
matchPremises :: ProofEnvironment -> [Fact] -> [[FactEntry]]
matchPremises env = matchPremisesPure (peFactIndex env)
