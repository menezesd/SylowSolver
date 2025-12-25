module Main where

import Criterion.Main
import Criterion.Types (Config(..))
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

import Auto (prove)
import Core
import Env
import Environment.Types
import Environment.Facts (addNewFacts)
import Predicates (group, order)
import Theorems
import Unification

-- Benchmark: Creating and populating environments
benchEnvCreation :: Benchmark
benchEnvCreation = bgroup "Environment Creation"
  [ bench "initEnv" $ nf (\n -> initEnv [] allTheorems Map.empty (group (sym "G"))) ()
  , bench "addNewFacts (1 fact)" $ nf addOneFact ()
  , bench "addNewFacts (10 facts)" $ nf addTenFacts ()
  , bench "addNewFacts (100 facts)" $ nf addHundredFacts ()
  ]
  where
    addOneFact () =
      let env = initEnv [] allTheorems Map.empty (group (sym "G"))
          facts = [NewConclusion (CFact (order (sym "G") (sym "6"))) [] Set.empty Nothing]
      in addNewFacts env facts

    addTenFacts () =
      let env = initEnv [] allTheorems Map.empty (group (sym "G"))
          facts = [ NewConclusion (CFact (Fact ("pred" ++ show i) [sym "x"])) [] Set.empty Nothing
                  | i <- [1..10 :: Int]
                  ]
      in addNewFacts env facts

    addHundredFacts () =
      let env = initEnv [] allTheorems Map.empty (group (sym "G"))
          facts = [ NewConclusion (CFact (Fact ("pred" ++ show i) [sym "x"])) [] Set.empty Nothing
                  | i <- [1..100 :: Int]
                  ]
      in addNewFacts env facts

-- Benchmark: Unification
benchUnification :: Benchmark
benchUnification = bgroup "Unification"
  [ bench "unify identical" $ nf unifyIdentical ()
  , bench "unify with 1 var" $ nf unifyOneVar ()
  , bench "unify with 5 vars" $ nf unifyFiveVars ()
  , bench "unify failure (name)" $ nf unifyFailName ()
  , bench "unify failure (arity)" $ nf unifyFailArity ()
  ]
  where
    unifyIdentical () =
      unify (Fact "foo" [sym "a", sym "b"]) (Fact "foo" [sym "a", sym "b"])

    unifyOneVar () =
      unify (Fact "foo" [var "X"]) (Fact "foo" [sym "a"])

    unifyFiveVars () =
      unify (Fact "foo" [var "A", var "B", var "C", var "D", var "E"])
            (Fact "foo" [sym "a", sym "b", sym "c", sym "d", sym "e"])

    unifyFailName () =
      unify (Fact "foo" []) (Fact "bar" [])

    unifyFailArity () =
      unify (Fact "foo" [sym "a"]) (Fact "foo" [sym "a", sym "b"])

-- Benchmark: Theorem matching
benchTheoremMatching :: Benchmark
benchTheoremMatching = bgroup "Theorem Matching"
  [ bench "match simple theorem" $ nf matchSimple ()
  , bench "match complex theorem" $ nf matchComplex ()
  ]
  where
    matchSimple () =
      let env = initEnv [] allTheorems Map.empty (group (sym "G"))
          (env', _) = addNewFacts env [NewConclusion (CFact (order (sym "G") (sym "6"))) [] Set.empty Nothing]
      in length (peFacts env')

    matchComplex () =
      let env = initEnv [] allTheorems Map.empty (group (sym "G"))
          facts = [ NewConclusion (CFact (order (sym "G") (sym "6"))) [] Set.empty Nothing
                  , NewConclusion (CFact (group (sym "G"))) [] Set.empty Nothing
                  ]
          (env', _) = addNewFacts env facts
      in length (peFacts env')

-- Benchmark: Small proof searches
benchSmallProofs :: Benchmark
benchSmallProofs = bgroup "Small Proofs"
  [ bench "order 1" $ nf proveOrder 1
  , bench "order 2" $ nf proveOrder 2
  , bench "order 3" $ nf proveOrder 3
  ]
  where
    proveOrder n = prove n 1000

-- Benchmark: Medium proof searches (with timeout protection)
benchMediumProofs :: Benchmark
benchMediumProofs = bgroup "Medium Proofs"
  [ bench "order 6" $ nf proveOrder 6
  , bench "order 10" $ nf proveOrder 10
  , bench "order 15" $ nf proveOrder 15
  ]
  where
    proveOrder n = prove n 1000

main :: IO ()
main = defaultMainWith config
  [ benchEnvCreation
  , benchUnification
  , benchTheoremMatching
  , benchSmallProofs
  , benchMediumProofs
  ]
  where
    -- Custom config with reasonable time limits
    config = defaultConfig
      { timeLimit = 10  -- 10 seconds per benchmark
      , resamples = 100  -- Number of resamples for bootstrap
      }
