{-# LANGUAGE DerivingStrategies #-}

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
  , ppArg
  , ppFact
  , argAtom
  ) where

import Data.List (intercalate)

-- Pretty-printing functions for Arg and Fact
ppArg :: Arg -> String
ppArg (Sym s) = s
ppArg (Var s) = "?" ++ s
ppArg (Exact s) = "'" ++ s ++ "'"
ppArg (Fresh s) = "_" ++ s
ppArg (Num n) = show n

ppFact :: Fact -> String
ppFact (Fact n args) = n ++ "(" ++ intercalate ", " (map ppArg args) ++ ")"

newtype FactId = FactId Int deriving stock (Eq, Ord, Show)
newtype DisjId = DisjId Int deriving stock (Eq, Ord, Show)

data Label
  = LFact FactId
  | LDisj DisjId
  deriving stock (Eq, Ord, Show)

data Arg
  = Sym String
  | Var String
  | Exact String
  | Fresh String
  | Num Int      -- Numeric argument for efficient number handling
  deriving stock (Eq, Ord, Show)

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

{-# INLINE argText #-}
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

-- Distinguish between numeric and string arguments
argAtom :: Arg -> Either Int String
argAtom (Num n) = Left n
argAtom a = Right (argText a)

-- FactKey: A key for indexing facts by name and arity
-- Replaces the repeated (String, Int) tuple pattern
data FactKey = FactKey
  { fkName :: String
  , fkArity :: Int
  } deriving stock (Eq, Ord, Show)

-- Extract the FactKey from a Fact
{-# INLINE factKey #-}
factKey :: Fact -> FactKey
factKey (Fact name args) = FactKey name (length args)

data Fact = Fact
  { factName :: String
  , factArgs :: [Arg]
  } deriving stock (Eq, Ord, Show)

data Disjunction = Disjunction
  { disjFacts :: [Fact]  -- Empty disjunction = FALSE
  } deriving stock (Eq, Show)

data Theorem = Theorem
  { theoremName :: String
  , theoremFacts :: [Fact]
  , theoremConcs :: [Fact]
  } deriving stock (Eq, Show)

data HyperTheorem = HyperTheorem
  { hyperName :: String
  , hyperFacts :: [Fact]
  , hyperRule :: [Fact] -> Maybe [Conclusion]
  }

-- Manual Show instance since hyperRule is a function
instance Show HyperTheorem where
  show ht = "HyperTheorem " ++ show (hyperName ht)

data Thm
  = Std Theorem
  | Hyper HyperTheorem

instance Show Thm where
  show (Std t) = "Std (" ++ show (theoremName t) ++ ")"
  show (Hyper t) = "Hyper (" ++ show (hyperName t) ++ ")"

-- A trigger represents a theorem premise that could be activated by a fact
data TheoremTrigger = TheoremTrigger
  { ttTheorem :: Thm                 -- The theorem
  , ttPremiseIndex :: Int            -- Which premise (0-based)
  , ttPremises :: [Fact]             -- All premises for this theorem
  }

data Conclusion
  = CFact Fact
  | CDisj Disjunction
  deriving stock (Eq, Show)

{-# INLINE thmName #-}
thmName :: Thm -> String
thmName (Std t) = theoremName t
thmName (Hyper t) = hyperName t

{-# INLINE thmFacts #-}
thmFacts :: Thm -> [Fact]
thmFacts (Std t) = theoremFacts t
thmFacts (Hyper t) = hyperFacts t
