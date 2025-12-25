module DomainTypes
  ( FactName(..)
  , TheoremName(..)
  , SymbolName(..)
  , VarName(..)
  , mkFactName
  , mkTheoremName
  , mkSymbolName
  , mkVarName
  , unFactName
  , unTheoremName
  , unSymbolName
  , unVarName
  ) where

-- Strong type for fact names
newtype FactName = FactName String
  deriving (Eq, Ord, Show)

-- Strong type for theorem names
newtype TheoremName = TheoremName String
  deriving (Eq, Ord, Show)

-- Strong type for symbol names
newtype SymbolName = SymbolName String
  deriving (Eq, Ord, Show)

-- Strong type for variable names
newtype VarName = VarName String
  deriving (Eq, Ord, Show)

-- Smart constructors
mkFactName :: String -> FactName
mkFactName = FactName

mkTheoremName :: String -> TheoremName
mkTheoremName = TheoremName

mkSymbolName :: String -> SymbolName
mkSymbolName = SymbolName

mkVarName :: String -> VarName
mkVarName = VarName

-- Extractors
unFactName :: FactName -> String
unFactName (FactName s) = s

unTheoremName :: TheoremName -> String
unTheoremName (TheoremName s) = s

unSymbolName :: SymbolName -> String
unSymbolName (SymbolName s) = s

unVarName :: VarName -> String
unVarName (VarName s) = s
