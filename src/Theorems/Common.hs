module Theorems.Common
  ( arg2
  , arg3
  , readInt
  ) where

import Core
import Text.Read (readMaybe)

readInt :: String -> Int
readInt s = maybe 0 id (readMaybe s)

arg2 :: Fact -> Maybe (Arg, Arg)
arg2 fact =
  case factArgs fact of
    [a, b] -> Just (a, b)
    _ -> Nothing

arg3 :: Fact -> Maybe (Arg, Arg, Arg)
arg3 fact =
  case factArgs fact of
    [a, b, c] -> Just (a, b, c)
    _ -> Nothing
