module Theorems
  ( thmList
  , thmNames
  , buildTriggerIndex
  ) where

import Core
import qualified Data.HashMap.Strict as HashMap
import Environment.Types (TriggerIndex)
import Theorems.Counting
import Theorems.Normalizer (normalizerEverythingImpliesNormal, normalizerSylowIntersection, normalSubgroupToNotSimple, ruleOutNormalizerOfIntersectionOrder)
import Theorems.Sylow

-- | Theorems ordered for efficient proof search:
--   1. Closing theorems (produce false()) - checked first to close branches early
--   2. Structural theorems (transform facts)
--   3. Expanding theorems (generate new facts/disjunctions) - checked last
thmList :: [Thm]
thmList =
  -- === Closing theorems (produce false()) ===
  [ simpleNotSimple           -- simple(G) ∧ not_simple(G) → false()
  , dividesContradiction      -- divides(n, m) where n ∤ m → false()
  , countingContradiction     -- Element counting overflow → false()
  , ruleOutMaxIntersections   -- Intersection contradictions → false()
  , ruleOutNormalizerOfIntersectionOrder

  -- === Structural theorems (transform/derive key facts) ===
  , singleSylowNotSimple      -- num_sylow = 1 → not_simple (feeds simpleNotSimple)
  , normalSubgroupToNotSimple -- normal proper subgroup → not_simple
  , lagrange                  -- Subgroup order divides group order
  , subgroupIndex             -- Index calculation
  , alternatingOrder          -- Order of alternating group

  -- === Expanding theorems (generate new facts/disjunctions) ===
  , sylowTheorem              -- Main disjunction generator
  , embedInAn                 -- Embed in alternating group
  , alternatingSimple         -- Alternating group simplicity
  , cosetAction               -- Coset actions
  , simpleGroupAction         -- Simple group actions
  , countOrderPkElements      -- Element counting bounds
  , multipleSylows            -- More than one Sylow subgroup
  , possibleMaxIntersections  -- Max intersection possibilities
  , intersectionOfSylows      -- Intersection of Sylow subgroups
  , normalizerSylowIntersection
  , normalizerEverythingImpliesNormal
  ]

thmNames :: HashMap.HashMap TheoremName Thm
thmNames = HashMap.fromList [(thmId thm, thm) | thm <- thmList]

-- Build trigger index for incremental theorem matching
buildTriggerIndex :: [Thm] -> TriggerIndex
buildTriggerIndex thms =
  let triggers = [ (factKey premise, TheoremTrigger thm i premises)
                 | thm <- thms
                 , let premises = thmFacts thm
                 , (i, premise) <- zip [0..] premises
                 ]
   in HashMap.fromListWith (++) [(k, [t]) | (k, t) <- triggers]
