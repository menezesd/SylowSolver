module Core
  ( Label(..)
  , FactId(..)
  , DisjId(..)
  , Arg(..)
  , sym
  , var
  , exact
  , fresh
  , argText
  , Fact(..)
  , Disjunction(..)
  , Theorem(..)
  , HyperTheorem(..)
  , Thm(..)
  , Conclusion(..)
  , thmName
  , thmFacts
  ) where

newtype FactId = FactId Int deriving (Eq, Ord, Show)
newtype DisjId = DisjId Int deriving (Eq, Ord, Show)

data Label
  = LFact FactId
  | LDisj DisjId
  deriving (Eq, Ord, Show)

data Arg
  = Sym String
  | Var String
  | Exact String
  | Fresh String
  deriving (Eq, Ord, Show)

sym :: String -> Arg
sym = Sym

var :: String -> Arg
var = Var

exact :: String -> Arg
exact = Exact

fresh :: String -> Arg
fresh = Fresh

argText :: Arg -> String
argText arg =
  case arg of
    Sym s -> s
    Var s -> s
    Exact s -> s
    Fresh s -> s

data Fact = Fact
  { factName :: String
  , factArgs :: [Arg]
  } deriving (Eq, Ord, Show)

data Disjunction = Disjunction
  { disjFacts :: [Fact]
  } deriving (Eq, Show)

data Theorem = Theorem
  { theoremName :: String
  , theoremFacts :: [Fact]
  , theoremConcs :: [Fact]
  } deriving (Eq, Show)

data HyperTheorem = HyperTheorem
  { hyperName :: String
  , hyperFacts :: [Fact]
  , hyperRule :: [Fact] -> [Conclusion]
  }

data Thm
  = Std Theorem
  | Hyper HyperTheorem

data Conclusion
  = CFact Fact
  | CDisj Disjunction

thmName :: Thm -> String
thmName (Std t) = theoremName t
thmName (Hyper t) = hyperName t

thmFacts :: Thm -> [Fact]
thmFacts (Std t) = theoremFacts t
thmFacts (Hyper t) = hyperFacts t
