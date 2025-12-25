module ConclusionDSL
  ( -- Re-export Conclusion type
    Conclusion(..)
  , Disjunction(..)
  -- DSL helpers
  , fact
  , disj
  , facts
  , factIf
  , disjIf
  , factsIf
  ) where

import Core

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
