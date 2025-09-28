-- | Spec.hs
--
-- Main test suite entry point for the Sylow Solver.

module Main where

import Test.Hspec
import NumberTheorySpec
import CoreSpec  
import AutoSpec

main :: IO ()
main = hspec $ do
  describe "NumberTheory" NumberTheorySpec.spec
  describe "Core" CoreSpec.spec
  describe "Auto" AutoSpec.spec