module NumberTheory
  ( isPrime
  , primesUpTo
  , divisors
  , maxPDivisor
  , primeFactors
  , primeFactorization
  , numSylow
  , pKillable
  , sylowKillable
  ) where

import Data.List (sort)

isqrt :: Int -> Int
isqrt n = go n
  where
    go x
      | x <= 0 = 0
      | otherwise =
          let y = (x + n `div` x) `div` 2
           in if y >= x then x else go y

isPrime :: Int -> Bool
isPrime n
  | n <= 1 = False
  | n <= 3 = True
  | even n = False
  | otherwise = go 3
  where
    r = isqrt n
    go i
      | i > r = True
      | n `mod` i == 0 = False
      | otherwise = go (i + 2)

primesUpTo :: Int -> [Int]
primesUpTo n
  | n < 2 = []
  | otherwise = sieve [2 .. n]
  where
    sieve [] = []
    sieve (p : xs)
      | p * p > n = p : xs
      | otherwise = p : sieve [x | x <- xs, x `mod` p /= 0]

divisors :: Int -> [Int]
divisors n
  | n <= 0 = []
  | otherwise = sort (concatMap pair [1 .. r])
  where
    r = isqrt n
    pair i
      | n `mod` i /= 0 = []
      | i * i == n = [i]
      | otherwise = [i, n `div` i]

maxPDivisor :: Int -> Int -> Int
maxPDivisor n p = go n 0
  where
    go m k
      | m `mod` p /= 0 = k
      | otherwise = go (m `div` p) (k + 1)

primeFactors :: Int -> [Int]
primeFactors n
  | n <= 1 = []
  | otherwise = go n 2 []
  where
    go m p acc
      | m == 1 = reverse acc
      | p * p > m = reverse (m : acc)
      | m `mod` p == 0 = go (dropFactor m p) (next p) (p : acc)
      | otherwise = go m (next p) acc
    dropFactor m p
      | m `mod` p == 0 = dropFactor (m `div` p) p
      | otherwise = m
    next 2 = 3
    next x = x + 2

primeFactorization :: Int -> [(Int, Int)]
primeFactorization n =
  [ (p, maxPDivisor n p)
  | p <- primeFactors n
  ]

numSylow :: Int -> Int -> [Int]
numSylow p n = [d | d <- divisors n, d `mod` p == 1]

pKillable :: Int -> Int -> Bool
pKillable p n = all (\d -> d == 1 || d `mod` p /= 1) (divisors n)

sylowKillable :: Int -> Bool
sylowKillable 1 = True
sylowKillable n =
  let ps = reverse (primeFactors n)
   in any (\p -> pKillable p n) ps
