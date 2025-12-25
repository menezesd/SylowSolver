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
  ) where

import Core
import Control.Monad (foldM)
import Environment.Types (TriggerIndex)
import qualified Data.Map.Strict as Map
import Env
import Unification

-- For a new fact, find all theorems that could be triggered
-- Returns list of (theorem, complete match) pairs
findTriggeredMatches :: ProofEnvironment -> FactEntry -> TriggerIndex -> [(Thm, [FactEntry])]
findTriggeredMatches env newFact triggerIndex =
  let fact = feFact newFact
      key = factKey fact
      triggers = Map.findWithDefault [] key triggerIndex

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
                  initialMatch = case unifyFact Map.empty targetPremise fact of
                    Left _ -> Nothing
                    Right subst -> Just (subst, [], newFact, [])
                    -- (subst, beforeMatches, targetMatch, afterMatches)
               in case initialMatch of
                    Nothing -> []
                    Just initial -> expandMatches initial beforePremises afterPremises
  where
    -- Match premises before and after the target using list monad with foldM
    expandMatches (subst, _beforeMatches, targetMatch, _afterMatches) beforePremises afterPremises =
      let -- Match a sequence of premises, threading substitution through
          matchAll :: (Substitution, [FactEntry]) -> [Fact] -> [(Substitution, [FactEntry])]
          matchAll start = foldM step start
            where
              step (s, matches) premise =
                [ (s', matches ++ [factEntry])
                | (factEntry, s') <- matchFactsToTemplate premise env s
                ]

       in do -- List monad: explores all matching possibilities
            (s', beforeFacts) <- matchAll (subst, []) beforePremises
            (_, afterFacts) <- matchAll (s', []) afterPremises
            return (beforeFacts ++ [targetMatch] ++ afterFacts)

-- Match a template fact against existing facts with an initial substitution
{-# INLINE matchFactsToTemplate #-}
matchFactsToTemplate :: Fact -> ProofEnvironment -> Substitution -> [(FactEntry, Substitution)]
matchFactsToTemplate template env initMap =
  let candidateFacts =
        Map.findWithDefault [] (factKey template) (peFactIndex env)
   in [ (factEntry, matchMap)
      | factEntry <- candidateFacts
      , let fact = feFact factEntry
      , Right matchMap <- [unifyFact initMap template fact]
      ]
