module Predicates
  ( PredName(..)
  , predNameText
  , customPred
  , pGroup
  , pOrder
  , pSylowOrder
  , pSylowPSubgroup
  , pAlternatingGroup
  , pNumSylow
  , pSimple
  , pNotSimple
  , pSubgroup
  , pDivides
  , pFalse
  , pIndex
  , pTransitiveAction
  , pOrderPkLowerBound
  , pMoreThanOneSylow
  , pIntersection
  , pNormalizer
  , pOrderLowerBound
  , pMaxSylowIntersection
  , pProperSubgroup
  , pNormal
  , pNormalizerOfSylowIntersection
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
  , orDisjunction
  -- Conclusion DSL (re-exported from Core)
  , Conclusion(..)
  , Disjunction(..)
  -- Conclusion helpers
  , fact
  , disj
  , facts
  , factIf
  , disjIf
  , factsIf
  ) where

import Core

pGroup, pOrder, pSylowOrder, pSylowPSubgroup :: PredName
pAlternatingGroup, pNumSylow, pSimple, pNotSimple :: PredName
pSubgroup, pDivides, pFalse, pIndex :: PredName
pTransitiveAction, pOrderPkLowerBound, pMoreThanOneSylow :: PredName
pIntersection, pNormalizer, pOrderLowerBound :: PredName
pMaxSylowIntersection, pProperSubgroup, pNormal :: PredName
pNormalizerOfSylowIntersection :: PredName

pGroup = PGroup
pOrder = POrder
pSylowOrder = PSylowOrder
pSylowPSubgroup = PSylowPSubgroup
pAlternatingGroup = PAlternatingGroup
pNumSylow = PNumSylow
pSimple = PSimple
pNotSimple = PNotSimple
pSubgroup = PSubgroup
pDivides = PDivides
pFalse = PFalse
pIndex = PIndex
pTransitiveAction = PTransitiveAction
pOrderPkLowerBound = POrderPkLowerBound
pMoreThanOneSylow = PMoreThanOneSylow
pIntersection = PIntersection
pNormalizer = PNormalizer
pOrderLowerBound = POrderLowerBound
pMaxSylowIntersection = PMaxSylowIntersection
pProperSubgroup = PProperSubgroup
pNormal = PNormal
pNormalizerOfSylowIntersection = PNormalizerOfSylowIntersection

group :: Arg -> Fact
group g = Fact pGroup [g]

order :: Arg -> Arg -> Fact
order g n = Fact pOrder [g, n]

sylowPOrder :: Arg -> Arg -> Arg -> Fact
sylowPOrder g p pk = Fact pSylowOrder [g, p, pk]

sylowPSubgroup :: Arg -> Arg -> Arg -> Fact
sylowPSubgroup psub p g = Fact pSylowPSubgroup [psub, p, g]

alternatingGroup :: Arg -> Arg -> Fact
alternatingGroup a n = Fact pAlternatingGroup [a, n]

numSylowFact :: Arg -> Arg -> Arg -> Fact
numSylowFact p g n = Fact pNumSylow [p, g, n]

simple :: Arg -> Fact
simple g = Fact pSimple [g]

notSimple :: Arg -> Fact
notSimple g = Fact pNotSimple [g]

subgroup :: Arg -> Arg -> Fact
subgroup h g = Fact pSubgroup [h, g]

divides :: Arg -> Arg -> Fact
divides m n = Fact pDivides [m, n]

falseFact :: Fact
falseFact = Fact pFalse []

index :: Arg -> Arg -> Arg -> Fact
index g h n = Fact pIndex [g, h, n]

transitiveAction :: Arg -> Arg -> Fact
transitiveAction g n = Fact pTransitiveAction [g, n]

orderPkLowerBound :: Arg -> Arg -> Arg -> Fact
orderPkLowerBound g p n = Fact pOrderPkLowerBound [g, p, n]

moreThanOneSylow :: Arg -> Arg -> Fact
moreThanOneSylow p g = Fact pMoreThanOneSylow [p, g]

intersection :: Arg -> Arg -> Arg -> Fact
intersection a b c = Fact pIntersection [a, b, c]

normalizer :: Arg -> Arg -> Arg -> Fact
normalizer g h k = Fact pNormalizer [g, h, k]

orderLowerBound :: Arg -> Arg -> Fact
orderLowerBound h n = Fact pOrderLowerBound [h, n]

maxSylowIntersection :: Arg -> Arg -> Arg -> Fact
maxSylowIntersection g p m = Fact pMaxSylowIntersection [g, p, m]

properSubgroup :: Arg -> Arg -> Fact
properSubgroup h g = Fact pProperSubgroup [h, g]

normal :: Arg -> Arg -> Fact
normal h g = Fact pNormal [h, g]

normalizerOfSylowIntersection :: Arg -> Arg -> Arg -> Fact
normalizerOfSylowIntersection p g t =
  Fact pNormalizerOfSylowIntersection [p, g, t]

orDisjunction :: Fact -> Fact -> Disjunction
orDisjunction f1 f2 = Disjunction [f1, f2]

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

-- | Conditionally create a fact conclusion
factIf :: Bool -> Fact -> [Conclusion]
factIf True f = [CFact f]
factIf False _ = []

-- | Conditionally create a disjunction conclusion
disjIf :: Bool -> [Fact] -> [Conclusion]
disjIf True fs = [CDisj (Disjunction fs)]
disjIf False _ = []

-- | Conditionally create multiple fact conclusions
factsIf :: Bool -> [Fact] -> [Conclusion]
factsIf True fs = map CFact fs
factsIf False _ = []
