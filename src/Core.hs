{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE StrictData #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}

-- | Core types for the Sylow solver.
--
-- == Error Handling Conventions
--
-- The codebase uses different error handling strategies based on context:
--
-- * __Unification__ ('Unification' module): Uses @Either UnificationError@
--   for explicit error types. Failures are expected during theorem matching.
--
-- * __Theorem rules__ ('Theorems.*' modules): Return @Maybe [Conclusion]@.
--   @Nothing@ means the rule doesn't apply; this is normal control flow.
--
-- * __Matching__ ('IncrementalMatching'): Returns empty lists @[]@ for no
--   matches. This allows easy composition with list operations.
--
-- * __State updates__ ('ProofMonad'): Uses @ProofM@ monad which wraps @State@.
--   Operations that can't fail use pure state updates; operations that may
--   fail (like finding a label) return @Maybe@ within the monad.
--
-- The general principle: explicit errors (@Either@) for debugging/diagnostics,
-- @Maybe@/empty list for expected "no result" cases in search.
--
module Core
  ( -- * Identity types
    Label(..)
  , FactId(..)
  , DisjId(..)
  , BranchIndex(..)
  , SymbolId(..)
  , Symbol(..)
  , unSymbol  -- Legacy accessor
    -- * Measure types
  , CaseDepth(..)
  , Arity(..)
    -- * Predicate names
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
    -- * Fact pattern synonyms
  , pattern GroupFact
  , pattern OrderFact
  , pattern SimpleFact
  , pattern NotSimpleFact
  , pattern NumSylowFact
  , pattern SubgroupFact
  , pattern DividesFact
  , pattern FalseFact
  , pattern IndexFact
  , pattern NormalFact
  , pattern SylowPSubgroupFact
    -- * Label formatting
  , labelText
    -- * GADT-based theorem representation
  , ThmKind(..)
  , TypedThm(..)
  , Thm
  , pattern Std
  , pattern Hyper
  , TheoremTrigger(..)
  , Conclusion(..)
  , conclusionFacts
  , thmName
  , thmId
  , thmFacts
  , thmConcs
  , thmRule
  , ppArg
  , ppFact
  , argAtom
  , matchSym
  ) where

import Data.List (intercalate)
import Data.Hashable (Hashable(..))

-- | Unique identifier for interned symbols.
newtype SymbolId = SymbolId { unSymbolId :: Int }
  deriving stock (Eq, Ord, Show)

instance Hashable SymbolId where
  hashWithSalt salt (SymbolId n) = hashWithSalt salt n

-- | Case analysis depth (0 = base level, increases with each disjunction).
newtype CaseDepth = CaseDepth { unCaseDepth :: Int }
  deriving stock (Eq, Ord, Show)

-- | Arity of a predicate (number of arguments).
newtype Arity = Arity { unArity :: Int }
  deriving stock (Eq, Ord, Show)

instance Hashable Arity where
  hashWithSalt salt (Arity n) = hashWithSalt salt n

-- | Opaque symbol identifier with stable text for rendering.
data Symbol = Symbol
  { symbolId :: {-# UNPACK #-} !SymbolId
  , symbolName :: !String
  } deriving stock (Show)

-- | Legacy accessor for backwards compatibility
unSymbol :: Symbol -> Int
unSymbol = unSymbolId . symbolId

instance Eq Symbol where
  s1 == s2 = symbolId s1 == symbolId s2

instance Ord Symbol where
  compare s1 s2 = compare (symbolId s1) (symbolId s2)

instance Hashable Symbol where
  hashWithSalt salt s = hashWithSalt salt (unSymbol s)

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

instance Hashable PredName where
  hashWithSalt salt pn = case pn of
    PGroup -> hashWithSalt salt (0 :: Int)
    POrder -> hashWithSalt salt (1 :: Int)
    PSylowOrder -> hashWithSalt salt (2 :: Int)
    PSylowPSubgroup -> hashWithSalt salt (3 :: Int)
    PAlternatingGroup -> hashWithSalt salt (4 :: Int)
    PNumSylow -> hashWithSalt salt (5 :: Int)
    PSimple -> hashWithSalt salt (6 :: Int)
    PNotSimple -> hashWithSalt salt (7 :: Int)
    PSubgroup -> hashWithSalt salt (8 :: Int)
    PDivides -> hashWithSalt salt (9 :: Int)
    PFalse -> hashWithSalt salt (10 :: Int)
    PIndex -> hashWithSalt salt (11 :: Int)
    PTransitiveAction -> hashWithSalt salt (12 :: Int)
    POrderPkLowerBound -> hashWithSalt salt (13 :: Int)
    PMoreThanOneSylow -> hashWithSalt salt (14 :: Int)
    PIntersection -> hashWithSalt salt (15 :: Int)
    PNormalizer -> hashWithSalt salt (16 :: Int)
    POrderLowerBound -> hashWithSalt salt (17 :: Int)
    PMaxSylowIntersection -> hashWithSalt salt (18 :: Int)
    PProperSubgroup -> hashWithSalt salt (19 :: Int)
    PNormal -> hashWithSalt salt (20 :: Int)
    PNormalizerOfSylowIntersection -> hashWithSalt salt (21 :: Int)
    PCustom s -> hashWithSalt salt (22 :: Int, s)

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
ppArg arg =
  case arg of
    Sym s -> symbolName s
    Var s -> "?" ++ s
    Exact s -> "'" ++ s ++ "'"
    Fresh s -> "_" ++ s
    Num n -> show n

ppFact :: Fact -> String
ppFact (Fact n args) =
  predNameText n ++ "(" ++ intercalate ", " (map ppArg args) ++ ")"

newtype FactId = FactId { unFactId :: Int } deriving stock (Eq, Ord, Show)
newtype DisjId = DisjId { unDisjId :: Int } deriving stock (Eq, Ord, Show)
newtype BranchIndex = BranchIndex { unBranchIndex :: Int } deriving stock (Eq, Ord, Show)

instance Hashable FactId where
  hashWithSalt salt (FactId n) = hashWithSalt salt n

instance Hashable DisjId where
  hashWithSalt salt (DisjId n) = hashWithSalt salt n

instance Hashable BranchIndex where
  hashWithSalt salt (BranchIndex n) = hashWithSalt salt n

data Label
  = LFact FactId
  | LDisj DisjId
  deriving stock (Eq, Ord, Show)

instance Hashable Label where
  hashWithSalt salt (LFact fid) = hashWithSalt salt (0 :: Int, fid)
  hashWithSalt salt (LDisj did) = hashWithSalt salt (1 :: Int, did)

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
sym s = Sym (Symbol (SymbolId (-1)) s)

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
    Sym s -> symbolName s
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
  , fkArity :: !Arity
  } deriving stock (Eq, Ord, Show)

newtype HashKey = HashKey { unHashKey :: Int }
  deriving stock (Eq, Ord, Show)

instance Hashable FactKey where
  hashWithSalt salt (FactKey n a) = hashWithSalt salt (n, unArity a)

-- Extract the FactKey from a Fact
{-# INLINE factKey #-}
factKey :: Fact -> FactKey
factKey (Fact name args) = FactKey name (Arity (length args))

data Fact = Fact
  { factName :: PredName
  , factArgs :: [Arg]
  } deriving stock (Eq, Ord, Show)

instance Hashable Fact where
  hashWithSalt salt (Fact n args) = hashWithSalt salt (n, length args)

-- | Pattern synonyms for common fact types (bidirectional)
-- These enable both construction and pattern matching

pattern GroupFact :: Arg -> Fact
pattern GroupFact g = Fact PGroup [g]

pattern OrderFact :: Arg -> Arg -> Fact
pattern OrderFact g n = Fact POrder [g, n]

pattern SimpleFact :: Arg -> Fact
pattern SimpleFact g = Fact PSimple [g]

pattern NotSimpleFact :: Arg -> Fact
pattern NotSimpleFact g = Fact PNotSimple [g]

pattern NumSylowFact :: Arg -> Arg -> Arg -> Fact
pattern NumSylowFact p g n = Fact PNumSylow [p, g, n]

pattern SubgroupFact :: Arg -> Arg -> Fact
pattern SubgroupFact h g = Fact PSubgroup [h, g]

pattern DividesFact :: Arg -> Arg -> Fact
pattern DividesFact m n = Fact PDivides [m, n]

pattern FalseFact :: Fact
pattern FalseFact = Fact PFalse []

pattern IndexFact :: Arg -> Arg -> Arg -> Fact
pattern IndexFact g h n = Fact PIndex [g, h, n]

pattern NormalFact :: Arg -> Arg -> Fact
pattern NormalFact h g = Fact PNormal [h, g]

pattern SylowPSubgroupFact :: Arg -> Arg -> Arg -> Fact
pattern SylowPSubgroupFact psub p g = Fact PSylowPSubgroup [psub, p, g]

data Disjunction = Disjunction
  { disjFacts :: [Fact]  -- Empty disjunction = FALSE
  } deriving stock (Eq, Show)

instance Hashable Disjunction where
  hashWithSalt salt (Disjunction fs) = hashWithSalt salt fs

-- | Format a label for display
labelText :: Label -> String
labelText (LFact (FactId n)) = "F" ++ show n
labelText (LDisj (DisjId n)) = "D" ++ show n

-- | Kind-level tag distinguishing theorem types
data ThmKind
  = ThmStandard   -- ^ Static theorem with fixed conclusions
  | ThmComputed   -- ^ Hyper-theorem with computed conclusions
  deriving stock (Eq, Show)

-- | GADT for type-safe theorem representation.
-- The phantom type 'k' encodes whether conclusions are static or computed.
data TypedThm (k :: ThmKind) where
  -- | Standard theorem: fixed premises → fixed conclusions
  MkStdThm
    :: TheoremName
    -> [Fact]  -- ^ Premises (patterns to match)
    -> [Fact]  -- ^ Conclusions (facts to derive)
    -> TypedThm 'ThmStandard

  -- | Hyper-theorem: premises + rule function → computed conclusions
  MkHyperThm
    :: TheoremName
    -> [Fact]  -- ^ Premises (patterns to match)
    -> ([Fact] -> Maybe [Conclusion])  -- ^ Rule that computes conclusions
    -> TypedThm 'ThmComputed

deriving stock instance Show (TypedThm 'ThmStandard)

instance Show (TypedThm 'ThmComputed) where
  show (MkHyperThm name _ _) = "MkHyperThm " ++ theoremNameText name

-- | Existential wrapper for heterogeneous theorem collections.
-- This allows mixing standard and hyper-theorems in lists.
data Thm where
  MkThm :: TypedThm k -> Thm

instance Show Thm where
  show (MkThm t) = case t of
    MkStdThm name _ _ -> "Std (" ++ theoremNameText name ++ ")"
    MkHyperThm name _ _ -> "Hyper (" ++ theoremNameText name ++ ")"

-- | Pattern synonym for standard theorems (backward compatibility)
pattern Std :: TheoremName -> [Fact] -> [Fact] -> Thm
pattern Std name prems concs = MkThm (MkStdThm name prems concs)

-- | Pattern synonym for hyper-theorems (backward compatibility)
pattern Hyper :: TheoremName -> [Fact] -> ([Fact] -> Maybe [Conclusion]) -> Thm
pattern Hyper name prems rule <- MkThm (MkHyperThm name prems rule)
  where Hyper name prems rule = MkThm (MkHyperThm name prems rule)

{-# COMPLETE Std, Hyper #-}

-- A trigger represents a theorem premise that could be activated by a fact
data TheoremTrigger = TheoremTrigger
  { ttTheorem :: Thm                           -- The theorem
  , ttPremiseIndex :: {-# UNPACK #-} !Int      -- Which premise (0-based)
  , ttPremises :: [Fact]                       -- All premises for this theorem
  }

data Conclusion
  = CFact Fact
  | CDisj Disjunction
  deriving stock (Eq, Show)

-- | Extract facts from a conclusion
{-# INLINE conclusionFacts #-}
conclusionFacts :: Conclusion -> [Fact]
conclusionFacts (CFact f) = [f]
conclusionFacts (CDisj (Disjunction fs)) = fs

{-# INLINE thmName #-}
thmName :: Thm -> String
thmName (Std name _ _) = theoremNameText name
thmName (Hyper name _ _) = theoremNameText name

{-# INLINE thmId #-}
thmId :: Thm -> TheoremName
thmId (Std name _ _) = name
thmId (Hyper name _ _) = name

{-# INLINE thmFacts #-}
thmFacts :: Thm -> [Fact]
thmFacts (Std _ prems _) = prems
thmFacts (Hyper _ prems _) = prems

-- | Get static conclusions from a standard theorem (Nothing for hyper-theorems)
{-# INLINE thmConcs #-}
thmConcs :: Thm -> Maybe [Fact]
thmConcs (Std _ _ concs) = Just concs
thmConcs (Hyper _ _ _) = Nothing

-- | Get the rule function from a hyper-theorem (Nothing for standard theorems)
{-# INLINE thmRule #-}
thmRule :: Thm -> Maybe ([Fact] -> Maybe [Conclusion])
thmRule (Std _ _ _) = Nothing
thmRule (Hyper _ _ rule) = Just rule
