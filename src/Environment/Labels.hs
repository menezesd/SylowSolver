module Environment.Labels
  ( newFactLabel
  , newDisjunctionLabel
  , disjunctionKey
  ) where

import Core
import Environment.Types
import qualified Data.HashMap.Strict as HashMap
import qualified Data.Set as Set

-- Build structural key from disjunction entry (DisjunctionKey defined in Types)
disjunctionKey :: DisjunctionEntry -> DisjunctionKey
disjunctionKey disj =
  let -- deFacts is already sorted by Fact's Ord instance (via Set.toAscList in Builders)
      facts = deFacts disj
      ancestors = Set.toAscList (deDisAncestors disj)
   in mkDisjunctionKey
        [(factName f, factArgs f) | f <- facts]
        (deConcThm disj)
        ancestors

-- Generate a new unique fact label
newFactLabel :: ProofEnvironment -> (FactId, ProofEnvironment)
newFactLabel env =
  let lbl = FactId (peCurFactNum env)
   in (lbl, updateGenState (\gs -> gs { gsCurFactNum = gsCurFactNum gs + 1 }) env)

-- Generate a new disjunction label (reuses existing if same key)
newDisjunctionLabel :: ProofEnvironment -> DisjunctionEntry -> (DisjId, ProofEnvironment)
newDisjunctionLabel env disj =
  let key = disjunctionKey disj
   in case HashMap.lookup key (peDisjLabels env) of
        Just existingId -> (existingId, env)
        Nothing ->
          let newId = DisjId (peCurDisjNum env)
              env' = updateGenState (\gs -> gs { gsCurDisjNum = gsCurDisjNum gs + 1 }) env
              env'' = updateFactDB (\db -> db { fdDisjLabels = HashMap.insert key newId (fdDisjLabels db) }) env'
           in (newId, env'')
