module Predicates
  ( PredName(..)
  , predNameText
  , customPred
  -- Fact constructors
  , group
  , order
  , sylowPOrder
  , sylowPSubgroup
  , alternatingGroup
  , numSylowFact
  , simple
  , notSimple
  , subgroup
  , divides
  , falseFact
  , index
  , transitiveAction
  , orderPkLowerBound
  , moreThanOneSylow
  , intersection
  , normalizer
  , orderLowerBound
  , maxSylowIntersection
  , properSubgroup
  , normal
  , normalizerOfSylowIntersection
  -- Conclusion DSL (re-exported from Core)
  , Conclusion(..)
  , Disjunction(..)
  -- Conclusion helpers
  , fact
  , disj
  , facts
  ) where

import Core

group :: Arg -> Fact
group g = Fact PGroup [g]

order :: Arg -> Arg -> Fact
order g n = Fact POrder [g, n]

sylowPOrder :: Arg -> Arg -> Arg -> Fact
sylowPOrder g p pk = Fact PSylowOrder [g, p, pk]

sylowPSubgroup :: Arg -> Arg -> Arg -> Fact
sylowPSubgroup psub p g = Fact PSylowPSubgroup [psub, p, g]

alternatingGroup :: Arg -> Arg -> Fact
alternatingGroup a n = Fact PAlternatingGroup [a, n]

numSylowFact :: Arg -> Arg -> Arg -> Fact
numSylowFact p g n = Fact PNumSylow [p, g, n]

simple :: Arg -> Fact
simple g = Fact PSimple [g]

notSimple :: Arg -> Fact
notSimple g = Fact PNotSimple [g]

subgroup :: Arg -> Arg -> Fact
subgroup h g = Fact PSubgroup [h, g]

divides :: Arg -> Arg -> Fact
divides m n = Fact PDivides [m, n]

falseFact :: Fact
falseFact = Fact PFalse []

index :: Arg -> Arg -> Arg -> Fact
index g h n = Fact PIndex [g, h, n]

transitiveAction :: Arg -> Arg -> Fact
transitiveAction g n = Fact PTransitiveAction [g, n]

orderPkLowerBound :: Arg -> Arg -> Arg -> Fact
orderPkLowerBound g p n = Fact POrderPkLowerBound [g, p, n]

moreThanOneSylow :: Arg -> Arg -> Fact
moreThanOneSylow p g = Fact PMoreThanOneSylow [p, g]

intersection :: Arg -> Arg -> Arg -> Fact
intersection a b c = Fact PIntersection [a, b, c]

normalizer :: Arg -> Arg -> Arg -> Fact
normalizer g h k = Fact PNormalizer [g, h, k]

orderLowerBound :: Arg -> Arg -> Fact
orderLowerBound h n = Fact POrderLowerBound [h, n]

maxSylowIntersection :: Arg -> Arg -> Arg -> Fact
maxSylowIntersection g p m = Fact PMaxSylowIntersection [g, p, m]

properSubgroup :: Arg -> Arg -> Fact
properSubgroup h g = Fact PProperSubgroup [h, g]

normal :: Arg -> Arg -> Fact
normal h g = Fact PNormal [h, g]

normalizerOfSylowIntersection :: Arg -> Arg -> Arg -> Fact
normalizerOfSylowIntersection p g t =
  Fact PNormalizerOfSylowIntersection [p, g, t]

-- Conclusion DSL helpers

-- | Create a single fact conclusion
fact :: Fact -> Conclusion
fact = CFact

-- | Create a disjunction conclusion from a list of facts
disj :: [Fact] -> Conclusion
disj = CDisj . Disjunction

-- | Create multiple fact conclusions from a list of facts
facts :: [Fact] -> [Conclusion]
facts = map CFact
