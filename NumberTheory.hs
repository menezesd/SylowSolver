-- | NumberTheory.hs
--
-- Number-theory utilities for the Sylow solver.
-- This module provides efficient helpers for primes, divisors and
-- prime factorizations used by the proof engine.
--
-- This is a Haskell port of the Python sylow2.py module.

module NumberTheory
  ( isPrime
  , primes
  , divisors
  , maxPDivisor
  , primeFactors
  , primeFactorization
  , prime
  , numSylow
  , pKillable
  , sylowKillable
  ) where

import Data.List (sort, nub)

-- | Return True if n is prime.
-- Uses simple deterministic trial division (sufficient for moderate n).
isPrime :: Int -> Bool
isPrime n
  | n <= 1 = False
  | n <= 3 = True
  | n `mod` 2 == 0 = False
  | otherwise = not $ any (\i -> n `mod` i == 0) [3, 5 .. isqrt n]
  where
    isqrt = floor . sqrt . fromIntegral

-- | Return list of primes up to and including n using a simple sieve.
primes :: Int -> [Int]
primes n
  | n < 2 = []
  | otherwise = sieve [2..n]
  where
    sieve [] = []
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

-- | Return the divisors of n in sorted order.
divisors :: Int -> [Int]
divisors n
  | n <= 0 = []
  | otherwise = sort $ concatMap getDivisorPair [1 .. isqrt n]
  where
    isqrt = floor . sqrt . fromIntegral
    getDivisorPair i
      | n `mod` i == 0 = 
          let j = n `div` i
          in if i == j then [i] else [i, j]
      | otherwise = []

-- | Return k maximal such that p^k divides n.
maxPDivisor :: Int -> Int -> Int
maxPDivisor n p = go n 0
  where
    go m k
      | m `mod` p == 0 = go (m `div` p) (k + 1)
      | otherwise = k

-- | Return the list of prime divisors of n in ascending order.
-- This is more efficient than testing every integer up to n.
primeFactors :: Int -> [Int]
primeFactors n
  | n <= 1 = []
  | otherwise = sort $ factor2 n []
  where
    factor2 m acc
      | m `mod` 2 == 0 = factor2 (removeFactors m 2) (2 : acc)
      | otherwise = factorOdd m 3 acc
    
    factorOdd m p acc
      | p * p > m = if m > 1 then m : acc else acc
      | m `mod` p == 0 = factorOdd (removeFactors m p) (p + 2) (p : acc)
      | otherwise = factorOdd m (p + 2) acc
    
    removeFactors m p
      | m `mod` p == 0 = removeFactors (m `div` p) p
      | otherwise = m

-- | Return prime factorization as a list of (prime, exponent).
-- Example: 12 -> [(2,2),(3,1)].
primeFactorization :: Int -> [(Int, Int)]
primeFactorization n = map (\p -> (p, maxPDivisor n p)) (nub $ primeFactors n)

-- | Compatibility wrapper for isPrime.
prime :: Int -> Bool
prime = isPrime

-- | Return divisors d of n with d ≡ 1 (mod p).
numSylow :: Int -> Int -> [Int]
numSylow p n = filter (\d -> d `mod` p == 1) (divisors n)

-- | Return True if there is no divisor d>1 of n with d ≡ 1 (mod p).
-- Check all divisors except 1.
pKillable :: Int -> Int -> Bool
pKillable p n = not $ any (\d -> d > 1 && d `mod` p == 1) (divisors n)

-- | Return True if there exists a prime p dividing n for which pKillable p n is True.
sylowKillable :: Int -> Bool
sylowKillable n
  | n == 1 = True
  | otherwise = any (`pKillable` n) (reverse $ primeFactors n)