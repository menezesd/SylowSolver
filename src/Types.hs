-- | Core data types for the Sylow solver
module Types where

import qualified Data.Heap as H
import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Future type-safety improvements (newtypes)
newtype DisjId = DisjId Int deriving (Eq, Ord, Show)
newtype AltIx = AltIx Int deriving (Eq, Ord, Show)
newtype GroupName = GroupName String deriving (Eq, Ord, Show)

-- Incremental typed values and predicates (not yet wired into engine)
data Value = Sym String | Nat Integer | SymGroup Integer | AltGroup Integer
  deriving (Eq, Ord, Show)

-- Encoding/decoding typed values into string args for backward compatibility
renderSymGroup :: Integer -> String
renderSymGroup n = "SymGroup:" ++ show n

renderAltGroup :: Integer -> String
renderAltGroup n = "AltGroup:" ++ show n

readInt :: String -> Maybe Integer
readInt str = case reads str of
  [(x, "")] -> Just x
  _ -> Nothing

parseValue :: String -> Maybe Value
parseValue s
  | Just num <- stripPrefix "SymGroup:" s, Just n <- readInt num = Just (SymGroup n)
  | Just num <- stripPrefix "AltGroup:" s, Just n <- readInt num = Just (AltGroup n)
  | otherwise = Nothing

parseSymGroup :: String -> Maybe Integer
parseSymGroup s =
  case parseValue s of
    Just (SymGroup n) -> Just n
    _ -> Nothing

parseAltGroup :: String -> Maybe Integer
parseAltGroup s =
  case parseValue s of
    Just (AltGroup n) -> Just n
    _ -> Nothing

-- local helpers (rely on Math/Errors via prelude for safeRead if imported)
-- we declare a minimal safeRead here to avoid cyclic deps
stripPrefix :: String -> String -> Maybe String
stripPrefix pre s = if take (length pre) s == pre then Just (drop (length pre) s) else Nothing

data Pred
  = PGroup
  | POrder
  | PNumSylow
  | PSylowOrder
  | PSylowPSubgroup
  | PMoreThanOneSylow
  | PMaxSylowIntersection
  | PIntersection
  | POrderPkLowerBound
  | PEmbedsInSym
  | PEmbedInAlt
  | PAlternatingGroup
  | PDivides
  | PFalse
  | PTransitiveAction
  | PSubgroup
  | PIndex
  | PNormalizer
  | PNormal
  | PSimple
  | PNotSimple
  | PIs
  | PNormalizerOfSylowIntersection
  deriving (Eq, Ord, Show)

-- Typed Fact placeholder for gradual migration
data TFact = TFact
  { tfPred :: Pred
  , tfArgs :: [Value]
  , tfDeps :: S.Set Dep
  , tfProv :: Maybe Provenance
  } deriving (Eq, Ord, Show)

-- Predicate name mapping (string <-> ADT)
predToString :: Pred -> String
predToString p = case p of
  PGroup -> "group"
  POrder -> "order"
  PNumSylow -> "numSylow"
  PSylowOrder -> "sylowOrder"
  PSylowPSubgroup -> "sylowPSubgroup"
  PMoreThanOneSylow -> "moreThanOneSylow"
  PMaxSylowIntersection -> "maxSylowIntersection"
  PIntersection -> "intersection"
  POrderPkLowerBound -> "orderPkLowerBound"
  PEmbedsInSym -> "embedsInSym"
  PEmbedInAlt -> "embedInAlt"
  PAlternatingGroup -> "alternatingGroup"
  PDivides -> "divides"
  PFalse -> "false"
  PTransitiveAction -> "transitiveAction"
  PSubgroup -> "subgroup"
  PIndex -> "index"
  PNormalizer -> "normalizer"
  PNormal -> "normal"
  PSimple -> "simple"
  PNotSimple -> "notSimple"
  PIs -> "is"
  PNormalizerOfSylowIntersection -> "normalizerOfSylowIntersection"

parsePred :: String -> Maybe Pred
parsePred s = case s of
  "group" -> Just PGroup
  "order" -> Just POrder
  "numSylow" -> Just PNumSylow
  "sylowOrder" -> Just PSylowOrder
  "sylowPSubgroup" -> Just PSylowPSubgroup
  "moreThanOneSylow" -> Just PMoreThanOneSylow
  "maxSylowIntersection" -> Just PMaxSylowIntersection
  "intersection" -> Just PIntersection
  "orderPkLowerBound" -> Just POrderPkLowerBound
  "embedsInSym" -> Just PEmbedsInSym
  "embedInAlt" -> Just PEmbedInAlt
  "alternatingGroup" -> Just PAlternatingGroup
  "divides" -> Just PDivides
  "false" -> Just PFalse
  "transitiveAction" -> Just PTransitiveAction
  "subgroup" -> Just PSubgroup
  "index" -> Just PIndex
  "normalizer" -> Just PNormalizer
  "normal" -> Just PNormal
  "simple" -> Just PSimple
  "notSimple" -> Just PNotSimple
  "is" -> Just PIs
  "normalizerOfSylowIntersection" -> Just PNormalizerOfSylowIntersection
  _ -> Nothing

-- Value render/parse helpers
renderValue :: Value -> String
renderValue v = case v of
  Sym s -> s
  Nat n -> show n
  SymGroup n -> renderSymGroup n
  AltGroup n -> renderAltGroup n

-- Best-effort parser that recognizes typed encodings and integers; else Sym
parseValueGeneric :: String -> Value
parseValueGeneric s = case parseValue s of
  Just v -> v
  Nothing -> case readInt s of
    Just n -> Nat n
    Nothing -> Sym s


mkFactP :: Pred -> [Value] -> Fact
mkFactP p vs = Fact p vs mempty Nothing

-- Attempt to decode a Fact into typed predicate and values (now trivial)
tryParseFact :: Fact -> Maybe (Pred, [Value])
tryParseFact (Fact p args _ _) = Just (p, args)

-- Core data model
data Fact = Fact
  { fPred  :: Pred
  , fArgs  :: [Value]
  , fDeps  :: S.Set Dep
  , fProv  :: Maybe Provenance
  } deriving (Eq, Ord, Show)

data Disj = Disj
  { dId    :: Int
  , dAlts  :: [Fact]
  , dDeps  :: S.Set Dep
  , dProv  :: Maybe Provenance
  , dLabel :: Maybe String
  } deriving (Eq, Ord, Show)

-- Structured dependency identifying a chosen alternative of a specific disjunction
data Dep = Dep { depDisj :: DisjId, depAlt :: AltIx }
  deriving (Eq, Ord, Show)

mkDep :: Int -> Int -> Dep
mkDep d a = Dep (DisjId d) (AltIx a)

depDisjInt :: Dep -> Int
depDisjInt (Dep (DisjId d) _) = d

depAltInt :: Dep -> Int
depAltInt (Dep _ (AltIx a)) = a

type Subst = M.Map String String

-- (removed DepRec prototype: Dep now provides this structure)

data Provenance = ProvHypothesis
                | ProvTheorem 
                  { thmName :: String
                  , parentFacts :: [Fact]
                  , fromDisj :: Maybe (Int, Int)
                  , provSubs :: Maybe Subst
                  }
                deriving (Eq, Ord, Show)

-- A pending theorem application
data App = App
  { appThmName :: String
  , appOutput  :: ThmOut
  , appDeps    :: S.Set Dep
  , appParents :: [Fact]
  , appSubs    :: Subst
  } deriving (Show)

-- Template matching now uses typed templates (TTemplate)

-- Theorem outputs
data ThmOut = TOFact Fact | TODisj [Fact] deriving (Eq, Show)

data Theorem = Theorem
  { tName :: String
  , tTemplate :: TTemplate
  , tApply :: [Fact] -> [ThmOut]
  , tCost :: Int
  }

-- Prover environment
data Env = Env
  { eFacts     :: S.Set Fact
  , eDisjs     :: M.Map Int Disj
  , eFrontier  :: S.Set Fact
  , eAppQueue  :: H.MinPrioHeap Int App
  , eNextDid   :: Int
  , eFresh     :: Int
  , eClosedAlts :: S.Set (Int, Int) -- (DisjId, AltIx) pairs that have been closed by contradiction
  } deriving (Show)

-- Engine configuration
data Engine = Engine 
  { thms :: [Theorem]
  , maxRounds :: Int
  , maxCaseSplit :: Int
  }

-- Tracing
data TraceEvent = TraceFactInserted 
  { teThm :: String
  , teFact :: Fact
  , teParentDeps :: S.Set Dep
  , teParents :: [Fact]
  , teSubs :: Subst
  }
  | TraceDisjInserted 
  { teThm :: String
  , teDid :: Int
  , teLabel :: Maybe String
  , teAlts :: [Fact]
  , teDeps :: S.Set Dep
  , teSubs :: Subst
  }
  deriving (Show)

-- Pretty printing state
data PrintState = PrintState 
  { psMap :: M.Map String Int
  , psNext :: Int
  }

-- Typed pattern language for templates (incremental adoption)
-- Pattern for a single argument: fixed typed value, named variable, or wildcard
data ValuePat
  = VFixed Value
  | VVar String
  | VWildcard
  deriving (Eq, Ord, Show)

-- Pattern for a single fact predicate with typed argument patterns
data TPattern = TPattern
  { tpName :: String
  , tpArgs :: [ValuePat]
  } deriving (Eq, Ord, Show)

-- Typed template: sequence of fact patterns
newtype TTemplate = TTemplate [TPattern] deriving (Eq, Show)

-- Helpers to build typed patterns
vpFixed :: Value -> ValuePat
vpFixed = VFixed

vpVar :: String -> ValuePat
vpVar = VVar

vpAny :: ValuePat
vpAny = VWildcard

mkTPattern :: String -> [ValuePat] -> TPattern
mkTPattern = TPattern

mkTTemplate :: [TPattern] -> TTemplate
mkTTemplate = TTemplate

-- Helper to define a theorem from a typed template
mkTheoremT :: String -> Int -> TTemplate -> ([Fact] -> [ThmOut]) -> Theorem
mkTheoremT name cost ttpl applyF = Theorem name ttpl applyF cost