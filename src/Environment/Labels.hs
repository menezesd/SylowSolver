module Environment.Labels
  ( newFactLabel
  , newDisjunctionLabel
  , canonicalDisjunctionSignature
  , disjLabelText
  , disjunctionKey
  ) where

import Core
import Environment.Types
import Environment.Accessors
import Data.List (sort, sortOn, intercalate)
import Data.Maybe (maybeToList)
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

-- Build structural key from disjunction entry (DisjunctionKey defined in Types)
disjunctionKey :: DisjunctionEntry -> DisjunctionKey
disjunctionKey disj =
  let facts = sortOn (\(Fact n a) -> (n, a)) (deFacts disj)
      ancestors = sort (Set.toList (deDisAncestors disj))
   in DisjunctionKey
        { dkFacts = [(factName f, factArgs f) | f <- facts]
        , dkThm = deConcThm disj
        , dkAncestors = ancestors
        }

-- Generate a new unique fact label
newFactLabel :: ProofEnvironment -> (ProofEnvironment, FactId)
newFactLabel env =
  let lbl = FactId (peCurFactNum env)
   in (updateGenState (\gs -> gs { gsCurFactNum = gsCurFactNum gs + 1 }) env, lbl)

-- Generate canonical signature for a disjunction
canonicalDisjunctionSignature :: DisjunctionEntry -> String
canonicalDisjunctionSignature disj =
  let sigs =
        sort
          [ factName f ++ ":" ++ intercalate "," (map argText (factArgs f))
          | f <- deFacts disj
          ]
      prov =
        map ("thm:" ++) (maybeToList (deConcThm disj))
          ++ [ "anc:" ++ intercalate "," ancLabels
             | not (Set.null (deDisAncestors disj))
             , let ancLabels = sort (Set.toList (Set.map disjLabelText (deDisAncestors disj)))
             ]
   in if null prov then intercalate "|" sigs else intercalate "|" sigs ++ "::" ++ intercalate "|" prov

-- Convert disjunction ID to text
disjLabelText :: (DisjId, Int) -> String
disjLabelText (DisjId n, _) = "D" ++ show n

-- Generate a new disjunction label (reuses existing if same key)
newDisjunctionLabel :: ProofEnvironment -> DisjunctionEntry -> (ProofEnvironment, DisjId)
newDisjunctionLabel env disj =
  let key = disjunctionKey disj
   in case Map.lookup key (peDisjLabels env) of
        Just existingId -> (env, existingId)
        Nothing ->
          let newId = DisjId (peCurDisjNum env)
              env' = updateGenState (\gs -> gs { gsCurDisjNum = gsCurDisjNum gs + 1 }) env
              env'' = updateFactDB (\db -> db { fdDisjLabels = Map.insert key newId (fdDisjLabels db) }) env'
           in (env'', newId)
