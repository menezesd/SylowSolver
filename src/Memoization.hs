{-# LANGUAGE BangPatterns #-}

-- | Thread-safe memoization for number theory functions.
--
-- == Safety of unsafePerformIO usage
--
-- This module uses 'unsafePerformIO' for global memoization caches.
-- The usage is safe because:
--
--   1. __Referential transparency__: The memoized functions are pure number
--      theory computations. The cache merely avoids recomputation; the result
--      is identical whether the value comes from cache or is freshly computed.
--
--   2. __Single initialization__: Each cache 'IORef' is created at most once
--      due to the 'NOINLINE' pragma, preventing the optimizer from duplicating
--      the initialization.
--
--   3. __Thread safety__: All cache operations use 'atomicModifyIORef'' which
--      provides atomic read-modify-write, preventing race conditions.
--
--   4. __No observable side effects__: From the caller's perspective, these
--      functions behave as pure functions. The internal caching is an
--      implementation detail that cannot affect program correctness.
--
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

import qualified Data.IntMap.Strict as IntMap
import Data.IORef
import System.IO.Unsafe (unsafePerformIO)
import NumberTheory

-- Cache statistics for measuring effectiveness
data CacheStats = CacheStats
  { csHits :: !Int
  , csMisses :: !Int
  , csCacheSize :: !Int
  } deriving (Show, Eq)

-- Global cache for divisors (using IntMap for efficiency)
-- SAFETY: NOINLINE ensures single initialization; see module header for full safety argument
{-# NOINLINE divisorsCache #-}
divisorsCache :: IORef (IntMap.IntMap [Int])
divisorsCache = unsafePerformIO (newIORef IntMap.empty)

-- Global cache for prime factors
-- SAFETY: See module header for unsafePerformIO safety argument
{-# NOINLINE primeFactorsCache #-}
primeFactorsCache :: IORef (IntMap.IntMap [Int])
primeFactorsCache = unsafePerformIO (newIORef IntMap.empty)

-- Global cache for prime factorization
-- SAFETY: See module header for unsafePerformIO safety argument
{-# NOINLINE primeFactorizationCache #-}
primeFactorizationCache :: IORef (IntMap.IntMap [(Int, Int)])
primeFactorizationCache = unsafePerformIO (newIORef IntMap.empty)

-- Global cache for isPrime
-- SAFETY: See module header for unsafePerformIO safety argument
{-# NOINLINE isPrimeCache #-}
isPrimeCache :: IORef (IntMap.IntMap Bool)
isPrimeCache = unsafePerformIO (newIORef IntMap.empty)

-- Global cache statistics
-- SAFETY: See module header for unsafePerformIO safety argument
{-# NOINLINE cacheStatsRef #-}
cacheStatsRef :: IORef CacheStats
cacheStatsRef = unsafePerformIO (newIORef (CacheStats 0 0 0))

-- | Memoize a pure function with Int keys using thread-safe global cache.
-- SAFETY: unsafePerformIO is safe here because:
--   - The function 'f' is pure (deterministic, no side effects)
--   - atomicModifyIORef' ensures thread-safe cache access
--   - The result is the same whether cached or computed
{-# INLINE memoizeInt #-}
memoizeInt :: IORef (IntMap.IntMap b) -> (Int -> b) -> Int -> b
memoizeInt cacheRef f x = unsafePerformIO $ do
  -- Atomic lookup-or-insert: check cache, compute if missing
  (result, isHit) <- atomicModifyIORef' cacheRef $ \cache ->
    case IntMap.lookup x cache of
      Just val -> (cache, (val, True))
      Nothing ->
        let !computed = f x
         in (IntMap.insert x computed cache, (computed, False))
  -- Update stats based on hit/miss
  atomicModifyIORef' cacheStatsRef $ \s ->
    if isHit
      then (s { csHits = csHits s + 1 }, ())
      else (s { csMisses = csMisses s + 1, csCacheSize = csCacheSize s + 1 }, ())
  return result

-- Memoized versions of number theory functions

divisorsMemo :: Int -> [Int]
divisorsMemo = memoizeInt divisorsCache divisors

primeFactorsMemo :: Int -> [Int]
primeFactorsMemo = memoizeInt primeFactorsCache primeFactors

primeFactorizationMemo :: Int -> [(Int, Int)]
primeFactorizationMemo = memoizeInt primeFactorizationCache primeFactorization

isPrimeMemo :: Int -> Bool
isPrimeMemo = memoizeInt isPrimeCache isPrime

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
  writeIORef divisorsCache IntMap.empty
  writeIORef primeFactorsCache IntMap.empty
  writeIORef primeFactorizationCache IntMap.empty
  writeIORef isPrimeCache IntMap.empty
  writeIORef cacheStatsRef (CacheStats 0 0 0)
