-- | Core data types for the Sylow solver
module Types where

import qualified Data.Map.Strict as M
import qualified Data.Set as S

-- Core data model
data Fact = Fact
  { fName  :: String
  , fArgs  :: [String]
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

type Dep = (Int, Int)
type Subst = M.Map String String

data Provenance = ProvHypothesis
                | ProvTheorem 
                  { thmName :: String
                  , parentFacts :: [Fact]
                  , fromDisj :: Maybe (Int, Int)
                  , provSubs :: Maybe Subst
                  }
                deriving (Eq, Ord, Show)

-- Template matching
newtype Template = Template [Fact] deriving (Eq, Show)

-- Theorem outputs
data ThmOut = TOFact Fact | TODisj [Fact] deriving (Eq, Show)

data Theorem = Theorem 
  { tName :: String
  , tTemplate :: Template
  , tApply :: [Fact] -> [ThmOut]
  }

-- Prover environment
data Env = Env
  { eFacts    :: S.Set Fact
  , eDisjs    :: M.Map Int Disj
  , eFrontier :: S.Set Fact
  , eNextDid  :: Int
  , eFresh    :: Int
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