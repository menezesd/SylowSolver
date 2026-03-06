module Theorems.Common
  ( -- Argument extractors
    arg2
  , arg3
  -- Numeric extractors (combine arg extraction with Num pattern matching)
  , withNum2
  , withNum3
  , withArg2Num
  , withArg3Num
  -- Helpers
  , asNum
  , guardList
  -- Theorem constructors
  , hyper
  , stdThm
  ) where

import Core

-- | Extract two arguments from a fact
{-# INLINE arg2 #-}
arg2 :: Fact -> Maybe (Arg, Arg)
arg2 fact =
  case factArgs fact of
    [a, b] -> Just (a, b)
    _ -> Nothing

-- | Extract three arguments from a fact
{-# INLINE arg3 #-}
arg3 :: Fact -> Maybe (Arg, Arg, Arg)
arg3 fact =
  case factArgs fact of
    [a, b, c] -> Just (a, b, c)
    _ -> Nothing

-- | Extract 2 args where the last is numeric, apply function if successful
{-# INLINE withNum2 #-}
withNum2 :: Fact -> (Arg -> Int -> a) -> Maybe a
withNum2 fact f =
  case factArgs fact of
    [a, Num n] -> Just (f a n)
    _ -> Nothing

-- | Extract 3 args where the last is numeric, apply function if successful
{-# INLINE withNum3 #-}
withNum3 :: Fact -> (Arg -> Arg -> Int -> a) -> Maybe a
withNum3 fact f =
  case factArgs fact of
    [a, b, Num n] -> Just (f a b n)
    _ -> Nothing

-- | Create a HyperTheorem (dynamic rule)
-- Uses the GADT-based Hyper pattern synonym
{-# INLINE hyper #-}
hyper :: String -> [Fact] -> ([Fact] -> Maybe [Conclusion]) -> Thm
hyper name premises rule = Hyper (mkTheoremName name) premises rule

-- | Create a standard Theorem (static rewrite rule)
-- Uses the GADT-based Std pattern synonym
{-# INLINE stdThm #-}
stdThm :: String -> [Fact] -> [Fact] -> Thm
stdThm name premises conclusions = Std (mkTheoremName name) premises conclusions

-- | Extract numeric value from an Arg
{-# INLINE asNum #-}
asNum :: Arg -> Maybe Int
asNum (Num n) = Just n
asNum _ = Nothing

-- | Extract 2 args from fact, convert last to Int, apply function
-- Combines arg2 + asNum pattern
{-# INLINE withArg2Num #-}
withArg2Num :: Fact -> (Arg -> Int -> a) -> Maybe a
withArg2Num fact f = do
  (a, b) <- arg2 fact
  n <- asNum b
  pure (f a n)

-- | Extract 3 args from fact, convert last to Int, apply function
-- Combines arg3 + asNum pattern
{-# INLINE withArg3Num #-}
withArg3Num :: Fact -> (Arg -> Arg -> Int -> a) -> Maybe a
withArg3Num fact f = do
  (a, b, c) <- arg3 fact
  n <- asNum c
  pure (f a b n)

-- | Conditional list: returns [x] if condition is true, else []
-- Replaces: if cond then [x] else []
{-# INLINE guardList #-}
guardList :: Bool -> a -> [a]
guardList True x = [x]
guardList False _ = []
