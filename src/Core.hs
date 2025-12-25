module Core
  ( Label(..)
  , FactId(..)
  , DisjId(..)
  , Arg(..)
  , sym
  , var
  , exact
  , fresh
  , num
  , argText
  , argInt
  , FactKey(..)
  , factKey
  , Fact(..)
  , Disjunction(..)
  , Theorem(..)
  , HyperTheorem(..)
  , Thm(..)
  , TheoremTrigger(..)
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
  | Num Int      -- Numeric argument for efficient number handling
  deriving (Eq, Ord, Show)

sym :: String -> Arg
sym = Sym

var :: String -> Arg
var = Var

exact :: String -> Arg
exact = Exact

fresh :: String -> Arg
fresh = Fresh

num :: Int -> Arg
num = Num

argText :: Arg -> String
argText arg =
  case arg of
    Sym s -> s
    Var s -> s
    Exact s -> s
    Fresh s -> s
    Num n -> show n

-- Extract integer from Num argument, or Nothing for other types
argInt :: Arg -> Maybe Int
argInt (Num n) = Just n
argInt _ = Nothing

-- FactKey: A key for indexing facts by name and arity
-- Replaces the repeated (String, Int) tuple pattern
data FactKey = FactKey
  { fkName :: String
  , fkArity :: Int
  } deriving (Eq, Ord, Show)

-- Extract the FactKey from a Fact
factKey :: Fact -> FactKey
factKey (Fact name args) = FactKey name (length args)

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

-- A trigger represents a theorem premise that could be activated by a fact
data TheoremTrigger = TheoremTrigger
  { ttTheorem :: Thm                 -- The theorem
  , ttPremiseIndex :: Int            -- Which premise (0-based)
  , ttPremises :: [Fact]             -- All premises for this theorem
  }

data Conclusion
  = CFact Fact
  | CDisj Disjunction

thmName :: Thm -> String
thmName (Std t) = theoremName t
thmName (Hyper t) = hyperName t

thmFacts :: Thm -> [Fact]
thmFacts (Std t) = theoremFacts t
thmFacts (Hyper t) = hyperFacts t
