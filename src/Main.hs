-- | Refactored Sylow Solver with separated concerns
{-# LANGUAGE DeriveGeneric #-}
module Main where

import SylowIO

-- Re-export main from SylowIO
main :: IO ()
main = SylowIO.main