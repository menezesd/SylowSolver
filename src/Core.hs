{-# LANGUAGE DerivingStrategies #-}

module Core
  ( Label(..)
  , FactId(..)
  , DisjId(..)
  , Symbol(..)
  , PredName(..)
  , predNameText
  , predNameFromText
  , customPred
  , TheoremName(..)
  , theoremNameText
  , mkTheoremName
  , theoremNameFromText
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
  , HashKey(..)
  , Fact(..)
  , Disjunction(..)
  , Theorem(..)
  , HyperTheorem(..)
  , Thm(..)
  , TheoremTrigger(..)
  , Conclusion(..)
  , thmName
  , thmId
  , thmFacts
  , ppArg
  , ppFact
  , argAtom
  , matchSym
  , ppArgWith
  , argTextWith
  , ppFactWith
  ) where

import Data.List (intercalate)
import Data.Hashable (Hashable(..))
import qualified Data.Map.Strict as Map

-- | Opaque symbol identifier with stable text for rendering.
data Symbol = Symbol
  { unSymbol :: Int
  , symbolName :: String
  } deriving stock (Show)

instance Eq Symbol where
  s1 == s2 = unSymbol s1 == unSymbol s2

instance Ord Symbol where
  compare s1 s2 = compare (unSymbol s1) (unSymbol s2)

instance Hashable Symbol where
  hashWithSalt salt (Symbol _ name) = hashWithSalt salt name

data PredName
  = PGroup
  | POrder
  | PSylowOrder
  | PSylowPSubgroup
  | PAlternatingGroup
  | PNumSylow
  | PSimple
  | PNotSimple
  | PSubgroup
  | PDivides
  | PFalse
  | PIndex
  | PTransitiveAction
  | POrderPkLowerBound
  | PMoreThanOneSylow
  | PIntersection
  | PNormalizer
  | POrderLowerBound
  | PMaxSylowIntersection
  | PProperSubgroup
  | PNormal
  | PNormalizerOfSylowIntersection
  | PCustom String
  deriving stock (Eq, Ord, Show)

predNameText :: PredName -> String
predNameText pn =
  case pn of
    PGroup -> "group"
    POrder -> "order"
    PSylowOrder -> "sylow_order"
    PSylowPSubgroup -> "sylow_p_subgroup"
    PAlternatingGroup -> "alternating_group"
    PNumSylow -> "num_sylow"
    PSimple -> "simple"
    PNotSimple -> "not_simple"
    PSubgroup -> "subgroup"
    PDivides -> "divides"
    PFalse -> "false"
    PIndex -> "index"
    PTransitiveAction -> "transitive_action"
    POrderPkLowerBound -> "order_pk_lower_bound"
    PMoreThanOneSylow -> "more_than_one_sylow"
    PIntersection -> "intersection"
    PNormalizer -> "normalizer"
    POrderLowerBound -> "order_lower_bound"
    PMaxSylowIntersection -> "max_sylow_intersection"
    PProperSubgroup -> "proper_subgroup"
    PNormal -> "normal"
    PNormalizerOfSylowIntersection -> "normalizer_of_sylow_intersection"
    PCustom s -> s

customPred :: String -> PredName
customPred = PCustom

predNameFromText :: String -> Maybe PredName
predNameFromText s =
  case s of
    "group" -> Just PGroup
    "order" -> Just POrder
    "sylow_order" -> Just PSylowOrder
    "sylow_p_subgroup" -> Just PSylowPSubgroup
    "alternating_group" -> Just PAlternatingGroup
    "num_sylow" -> Just PNumSylow
    "simple" -> Just PSimple
    "not_simple" -> Just PNotSimple
    "subgroup" -> Just PSubgroup
    "divides" -> Just PDivides
    "false" -> Just PFalse
    "index" -> Just PIndex
    "transitive_action" -> Just PTransitiveAction
    "order_pk_lower_bound" -> Just POrderPkLowerBound
    "more_than_one_sylow" -> Just PMoreThanOneSylow
    "intersection" -> Just PIntersection
    "normalizer" -> Just PNormalizer
    "order_lower_bound" -> Just POrderLowerBound
    "max_sylow_intersection" -> Just PMaxSylowIntersection
    "proper_subgroup" -> Just PProperSubgroup
    "normal" -> Just PNormal
    "normalizer_of_sylow_intersection" -> Just PNormalizerOfSylowIntersection
    _ -> Nothing

newtype TheoremName = TheoremName { unTheoremName :: String }
  deriving stock (Eq, Ord, Show)
instance Hashable TheoremName where
  hashWithSalt salt (TheoremName n) = hashWithSalt salt n

theoremNameText :: TheoremName -> String
theoremNameText = unTheoremName

mkTheoremName :: String -> TheoremName
mkTheoremName = TheoremName

theoremNameFromText :: String -> TheoremName
theoremNameFromText = mkTheoremName

-- Pretty-printing functions for Arg and Fact
ppArg :: Arg -> String
ppArg = ppArgWith Map.empty

ppArgWith :: Map.Map Int String -> Arg -> String
ppArgWith tbl arg =
  case arg of
    Sym s -> Map.findWithDefault (symbolName s) (unSymbol s) tbl
    Var s -> "?" ++ s
    Exact s -> "'" ++ s ++ "'"
    Fresh s -> "_" ++ s
    Num n -> show n

ppFact :: Fact -> String
ppFact = ppFactWith Map.empty

ppFactWith :: Map.Map Int String -> Fact -> String
ppFactWith tbl (Fact n args) =
  predNameText n ++ "(" ++ intercalate ", " (map (ppArgWith tbl) args) ++ ")"

newtype FactId = FactId Int deriving stock (Eq, Ord, Show)
newtype DisjId = DisjId Int deriving stock (Eq, Ord, Show)

data Label
  = LFact FactId
  | LDisj DisjId
  deriving stock (Eq, Ord, Show)

data Arg
  = Sym Symbol
  | Var String
  | Exact String
  | Fresh String
  | Num Int      -- Numeric argument for efficient number handling
  deriving stock (Eq, Ord, Show)

instance Hashable Arg where
  hashWithSalt salt arg =
    case arg of
      Sym s -> hashWithSalt salt (0 :: Int, unSymbol s)
      Var s -> hashWithSalt salt (1 :: Int, s)
      Exact s -> hashWithSalt salt (2 :: Int, s)
      Fresh s -> hashWithSalt salt (3 :: Int, s)
      Num n -> hashWithSalt salt (4 :: Int, n)

sym :: String -> Arg
sym s = Sym (Symbol (-1) s)

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
argText = argTextWith Map.empty

argTextWith :: Map.Map Int String -> Arg -> String
argTextWith tbl arg =
  case arg of
    Sym s -> Map.findWithDefault (symbolName s) (unSymbol s) tbl
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

-- | Extract a concrete symbol from an argument when present.
matchSym :: Arg -> Maybe Symbol
matchSym (Sym s) = Just s
matchSym _ = Nothing

-- FactKey: A key for indexing facts by name and arity
-- Replaces the repeated (String, Int) tuple pattern
data FactKey = FactKey
  { fkName :: PredName
  , fkArity :: Int
  } deriving stock (Eq, Ord, Show)

newtype HashKey = HashKey { unHashKey :: Int }
  deriving stock (Eq, Ord, Show)

instance Hashable FactKey where
  hashWithSalt salt (FactKey n a) = hashWithSalt salt (predNameText n, a)

-- Extract the FactKey from a Fact
{-# INLINE factKey #-}
factKey :: Fact -> FactKey
factKey (Fact name args) = FactKey name (length args)

data Fact = Fact
  { factName :: PredName
  , factArgs :: [Arg]
  } deriving stock (Eq, Ord, Show)

instance Hashable Fact where
  hashWithSalt salt (Fact n args) = hashWithSalt salt (predNameText n, length args)

data Disjunction = Disjunction
  { disjFacts :: [Fact]  -- Empty disjunction = FALSE
  } deriving stock (Eq, Show)

instance Hashable Disjunction where
  hashWithSalt salt (Disjunction fs) = hashWithSalt salt fs

data Theorem = Theorem
  { theoremName :: TheoremName
  , theoremFacts :: [Fact]
  , theoremConcs :: [Fact]
  } deriving stock (Eq, Show)

data HyperTheorem = HyperTheorem
  { hyperName :: TheoremName
  , hyperFacts :: [Fact]
  , hyperRule :: [Fact] -> Maybe [Conclusion]
  }

-- Manual Show instance since hyperRule is a function
instance Show HyperTheorem where
  show ht = "HyperTheorem " ++ theoremNameText (hyperName ht)

data Thm
  = Std Theorem
  | Hyper HyperTheorem

instance Show Thm where
  show (Std t) = "Std (" ++ theoremNameText (theoremName t) ++ ")"
  show (Hyper t) = "Hyper (" ++ theoremNameText (hyperName t) ++ ")"

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
thmName (Std t) = theoremNameText (theoremName t)
thmName (Hyper t) = theoremNameText (hyperName t)

thmId :: Thm -> TheoremName
thmId (Std t) = theoremName t
thmId (Hyper t) = hyperName t

{-# INLINE thmFacts #-}
thmFacts :: Thm -> [Fact]
thmFacts (Std t) = theoremFacts t
thmFacts (Hyper t) = hyperFacts t
