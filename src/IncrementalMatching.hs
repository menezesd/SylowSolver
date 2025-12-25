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
  ( findTriggeredMatches
  , matchFactsToTemplate
  , matchPremises
  , matchPremisesWithSubst
  ) where

import Core
import Data.List (foldl')
import Data.Hashable (hash)
import Environment.Types (TriggerIndex)
import qualified Data.Map.Strict as Map
import qualified Data.HashMap.Strict as HashMap
import qualified Data.IntMap.Strict as IntMap
import Env
import Environment.Types (peFactIndex)
import Unification

-- For a new fact, find all theorems that could be triggered
-- Returns list of (theorem, complete match) pairs
findTriggeredMatches :: ProofEnvironment -> FactEntry -> TriggerIndex -> [(Thm, [FactEntry])]
findTriggeredMatches env newFact triggerIndex =
  let fact = feFact newFact
      key = factKey fact
      triggers = HashMap.lookupDefault [] key triggerIndex

      -- For each trigger, try to complete the match
      tryTrigger trigger =
        let premises = ttPremises trigger
            triggerIdx = ttPremiseIndex trigger
            thm = ttTheorem trigger

            -- Try to match the new fact at position triggerIdx
            matchResults = matchNewFactAtPosition env newFact premises triggerIdx
         in [(thm, match) | match <- matchResults]

   in concatMap tryTrigger triggers

-- Match premises with a specific fact at a given position
-- Returns list of complete matches where all premises are satisfied
matchNewFactAtPosition :: ProofEnvironment -> FactEntry -> [Fact] -> Int -> [[FactEntry]]
matchNewFactAtPosition env newFact premises targetIdx
  | targetIdx < 0 || targetIdx >= length premises = []
  | otherwise =
      let -- Split premises: before target, target itself, after target
          (beforePremises, targetAndAfter) = splitAt targetIdx premises
       in case targetAndAfter of
            [] -> []  -- Safety: shouldn't happen due to bounds check, but handle gracefully
            (targetPremise : afterPremises) ->
              -- Try to unify the new fact with the target premise
              let fact = feFact newFact
               in case unifyFact Map.empty targetPremise fact of
                    Left _ -> []
                    Right subst ->
                      [ matchedFacts
                      | (substBefore, beforeFacts) <- matchPremisesWithSubst env subst [] beforePremises
                      , (_substAfter, fullFacts) <- matchPremisesWithSubst env substBefore (beforeFacts ++ [newFact]) afterPremises
                      , let matchedFacts = fullFacts
                      ]

-- Match a template fact against existing facts with an initial substitution
{-# INLINE matchFactsToTemplate #-}
matchFactsToTemplate :: Fact -> ProofEnvironment -> Substitution -> [(FactEntry, Substitution)]
matchFactsToTemplate template env initMap =
  let candidateFacts =
        IntMap.findWithDefault [] (hash template) (peFactIndex env)
   in [ (factEntry, matchMap)
      | factEntry <- candidateFacts
      , factKey (feFact factEntry) == factKey template
      , let fact = feFact factEntry
      , Right matchMap <- [unifyFact initMap template fact]
      ]

-- Match a sequence of premises, threading substitution and accumulating matched facts.
-- Returns all possible matches alongside the final substitution.
matchPremisesWithSubst :: ProofEnvironment -> Substitution -> [FactEntry] -> [Fact] -> [(Substitution, [FactEntry])]
matchPremisesWithSubst env initSubst seedFacts templates =
  foldl' step [(initSubst, seedFacts)] templates
  where
    step acc template =
      [ (subst', facts ++ [factEntry])
      | (subst, facts) <- acc
      , (factEntry, subst') <- matchFactsToTemplate template env subst
      ]

-- Convenience wrapper when the caller does not care about the final substitution.
matchPremises :: ProofEnvironment -> [Fact] -> [[FactEntry]]
matchPremises env templates =
  [ facts
  | (_subst, facts) <- matchPremisesWithSubst env Map.empty [] templates
  ]
