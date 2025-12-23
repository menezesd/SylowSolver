module Predicates
  ( group
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
  , orDisjunction
  ) where

import Core

group :: Arg -> Fact
group g = Fact "group" [g]

order :: Arg -> Arg -> Fact
order g n = Fact "order" [g, n]

sylowPOrder :: Arg -> Arg -> Arg -> Fact
sylowPOrder g p pk = Fact "sylow_order" [g, p, pk]

sylowPSubgroup :: Arg -> Arg -> Arg -> Fact
sylowPSubgroup psub p g = Fact "sylow_p_subgroup" [psub, p, g]

alternatingGroup :: Arg -> Arg -> Fact
alternatingGroup a n = Fact "alternating_group" [a, n]

numSylowFact :: Arg -> Arg -> Arg -> Fact
numSylowFact p g n = Fact "num_sylow" [p, g, n]

simple :: Arg -> Fact
simple g = Fact "simple" [g]

notSimple :: Arg -> Fact
notSimple g = Fact "not_simple" [g]

subgroup :: Arg -> Arg -> Fact
subgroup h g = Fact "subgroup" [h, g]

divides :: Arg -> Arg -> Fact
divides m n = Fact "divides" [m, n]

falseFact :: Fact
falseFact = Fact "false" []

index :: Arg -> Arg -> Arg -> Fact
index g h n = Fact "index" [g, h, n]

transitiveAction :: Arg -> Arg -> Fact
transitiveAction g n = Fact "transitive_action" [g, n]

orderPkLowerBound :: Arg -> Arg -> Arg -> Fact
orderPkLowerBound g p n = Fact "order_pk_lower_bound" [g, p, n]

moreThanOneSylow :: Arg -> Arg -> Fact
moreThanOneSylow p g = Fact "more_than_one_sylow" [p, g]

intersection :: Arg -> Arg -> Arg -> Fact
intersection a b c = Fact "intersection" [a, b, c]

normalizer :: Arg -> Arg -> Arg -> Fact
normalizer g h k = Fact "normalizer" [g, h, k]

orderLowerBound :: Arg -> Arg -> Fact
orderLowerBound h n = Fact "order_lower_bound" [h, n]

maxSylowIntersection :: Arg -> Arg -> Arg -> Fact
maxSylowIntersection g p m = Fact "max_sylow_intersection" [g, p, m]

properSubgroup :: Arg -> Arg -> Fact
properSubgroup h g = Fact "proper_subgroup" [h, g]

normal :: Arg -> Arg -> Fact
normal h g = Fact "normal" [h, g]

normalizerOfSylowIntersection :: Arg -> Arg -> Arg -> Fact
normalizerOfSylowIntersection p g t =
  Fact "normalizer_of_sylow_intersection" [p, g, t]

orDisjunction :: Fact -> Fact -> Disjunction
orDisjunction f1 f2 = Disjunction [f1, f2]
