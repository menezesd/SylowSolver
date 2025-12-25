module IncrementalMatching
  ( findTriggeredMatches
  ) where

import Core
import Environment.Types (TriggerIndex)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
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
          targetPremise = head targetAndAfter
          afterPremises = tail targetAndAfter

          -- Try to unify the new fact with the target premise
          fact = feFact newFact
          initialMatch = case unifyFact Map.empty targetPremise fact of
            Left _ -> Nothing
            Right subst -> Just (subst, [], newFact, [])
            -- (subst, beforeMatches, targetMatch, afterMatches)

       in case initialMatch of
            Nothing -> []
            Just initial -> expandMatches initial beforePremises afterPremises
  where
    -- Match premises before and after the target
    expandMatches (subst, beforeMatches, targetMatch, afterMatches) beforePremises afterPremises =
      -- Match all "before" premises, accumulating substitutions and matches
      let matchPremises :: [(Substitution, [FactEntry])] -> [Fact] -> [(Substitution, [FactEntry])]
          matchPremises acc [] = acc
          matchPremises acc (premise : rest) =
            let expanded = [ (s', matches ++ [factEntry])
                           | (s, matches) <- acc
                           , (factEntry, s') <- matchFactsToTemplate premise env s
                           ]
             in matchPremises expanded rest

          -- Match before premises
          afterBefore = matchPremises [(subst, [])] beforePremises

          -- For each "before" result, match after premises
          matchAfterPremises :: (Substitution, [FactEntry]) -> [(Substitution, [FactEntry], [FactEntry])]
          matchAfterPremises (s, beforeFacts) =
            let afterResults = matchPremises [(s, [])] afterPremises
             in [(s', beforeFacts, afterFacts) | (s', afterFacts) <- afterResults]

          fullyMatched = concatMap matchAfterPremises afterBefore

          -- Reconstruct in premise order: before ++ [target] ++ after
          buildResult (_, bm, am) = bm ++ [targetMatch] ++ am

       in map buildResult fullyMatched

-- Match a template fact against existing facts with an initial substitution
matchFactsToTemplate :: Fact -> ProofEnvironment -> Substitution -> [(FactEntry, Substitution)]
matchFactsToTemplate template env initMap =
  let candidateFacts =
        Map.findWithDefault [] (factKey template) (peFactIndex env)
   in [ (factEntry, matchMap)
      | factEntry <- candidateFacts
      , let fact = feFact factEntry
      , Right matchMap <- [unifyFact initMap template fact]
      ]
