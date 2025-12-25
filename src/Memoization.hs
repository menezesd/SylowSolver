{-# LANGUAGE BangPatterns #-}

module Memoization
  ( -- * Memoized number theory functions
    divisorsMemo
  , primeFactorsMemo
  , primeFactorizationMemo
  , isPrimeMemo
  , numSylowMemo
  , pKillableMemo
  , sylowKillableMemo

  -- * Cache statistics (for benchmarking)
  , getCacheStats
  , resetCacheStats
  , CacheStats(..)
  ) where

import qualified Data.Map.Strict as Map
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import NumberTheory

-- Cache statistics for measuring effectiveness
data CacheStats = CacheStats
  { csHits :: !Int
  , csMisses :: !Int
  , csCacheSize :: !Int
  } deriving (Show, Eq)

-- Global cache for divisors
{-# NOINLINE divisorsCache #-}
divisorsCache :: IORef (Map.Map Int [Int])
divisorsCache = unsafePerformIO (newIORef Map.empty)

-- Global cache for prime factors
{-# NOINLINE primeFactorsCache #-}
primeFactorsCache :: IORef (Map.Map Int [Int])
primeFactorsCache = unsafePerformIO (newIORef Map.empty)

-- Global cache for prime factorization
{-# NOINLINE primeFactorizationCache #-}
primeFactorizationCache :: IORef (Map.Map Int [(Int, Int)])
primeFactorizationCache = unsafePerformIO (newIORef Map.empty)

-- Global cache for isPrime
{-# NOINLINE isPrimeCache #-}
isPrimeCache :: IORef (Map.Map Int Bool)
isPrimeCache = unsafePerformIO (newIORef Map.empty)

-- Global cache statistics
{-# NOINLINE cacheStatsRef #-}
cacheStatsRef :: IORef CacheStats
cacheStatsRef = unsafePerformIO (newIORef (CacheStats 0 0 0))

-- Helper to memoize a function
memoize :: (Ord a) => IORef (Map.Map a b) -> (a -> b) -> a -> b
memoize cacheRef f x = unsafePerformIO $ do
  cache <- readIORef cacheRef
  case Map.lookup x cache of
    Just result -> do
      -- Record cache hit
      modifyIORef' cacheStatsRef $ \s -> s { csHits = csHits s + 1 }
      return result
    Nothing -> do
      -- Compute and cache result
      let !result = f x
      modifyIORef' cacheRef (Map.insert x result)
      -- Record cache miss
      modifyIORef' cacheStatsRef $ \s -> s
        { csMisses = csMisses s + 1
        , csCacheSize = csCacheSize s + 1
        }
      return result

-- Memoized versions of number theory functions

divisorsMemo :: Int -> [Int]
divisorsMemo = memoize divisorsCache divisors

primeFactorsMemo :: Int -> [Int]
primeFactorsMemo = memoize primeFactorsCache primeFactors

primeFactorizationMemo :: Int -> [(Int, Int)]
primeFactorizationMemo = memoize primeFactorizationCache primeFactorization

isPrimeMemo :: Int -> Bool
isPrimeMemo = memoize isPrimeCache isPrime

-- Derived memoized functions that use the cached primitives

numSylowMemo :: Int -> Int -> [Int]
numSylowMemo p n = [d | d <- divisorsMemo n, d `mod` p == 1]

pKillableMemo :: Int -> Int -> Bool
pKillableMemo p n = all (\d -> d == 1 || d `mod` p /= 1) (divisorsMemo n)

sylowKillableMemo :: Int -> Bool
sylowKillableMemo 1 = True
sylowKillableMemo n =
  let ps = reverse (primeFactorsMemo n)
   in any (\p -> pKillableMemo p n) ps

-- Cache statistics functions

getCacheStats :: IO CacheStats
getCacheStats = readIORef cacheStatsRef

resetCacheStats :: IO ()
resetCacheStats = do
  writeIORef divisorsCache Map.empty
  writeIORef primeFactorsCache Map.empty
  writeIORef primeFactorizationCache Map.empty
  writeIORef isPrimeCache Map.empty
  writeIORef cacheStatsRef (CacheStats 0 0 0)
