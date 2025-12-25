module ArgUtils
  ( argName
  , isBindable
  , isConcrete
  , isExact
  , isVar
  , isSym
  , isFresh
  , isNum
  , matchMode
  , MatchMode(..)
  ) where

import Core

-- Get the text content of any Arg
argName :: Arg -> String
argName = argText

-- Check if an arg can be bound to a value (Var or Fresh)
isBindable :: Arg -> Bool
isBindable (Var _) = True
isBindable (Fresh _) = True
isBindable _ = False

-- Check if an arg is concrete (Sym or Exact)
isConcrete :: Arg -> Bool
isConcrete (Sym _) = True
isConcrete (Exact _) = True
isConcrete _ = False

-- Type-specific checks
isExact :: Arg -> Bool
isExact (Exact _) = True
isExact _ = False

isVar :: Arg -> Bool
isVar (Var _) = True
isVar _ = False

isSym :: Arg -> Bool
isSym (Sym _) = True
isSym _ = False

isFresh :: Arg -> Bool
isFresh (Fresh _) = True
isFresh _ = False

isNum :: Arg -> Bool
isNum (Num _) = True
isNum _ = False

-- Match mode for pattern matching
data MatchMode
  = ExactMatch String    -- Must match exactly
  | BindableVar String   -- Can bind to anything
  | ConcreteValue String -- Concrete symbol
  deriving (Eq, Show)

-- Determine the match mode for an argument
matchMode :: Arg -> MatchMode
matchMode (Exact name) = ExactMatch name
matchMode (Var name) = BindableVar name
matchMode (Fresh name) = BindableVar name
matchMode (Sym name) = ConcreteValue name
matchMode (Num n) = ConcreteValue (show n)
