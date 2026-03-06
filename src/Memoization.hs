{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleInstances #-}

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
  , divisorsMemoWith
  , primeFactorsMemoWith
  , primeFactorizationMemoWith
  , isPrimeMemoWith
  , numSylowMemoWith
  , pKillableMemoWith
  , sylowKillableMemoWith

  -- * Cache statistics (for benchmarking)
  , getCacheStats
  , resetCacheStats
  , getCacheStatsWith
  , resetCacheStatsWith
  , CacheStats(..)
  , MemoStore(..)
  , newMemoStore
  , globalMemoStore
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

class Memoizable a
instance Memoizable [Int]
instance Memoizable [(Int, Int)]
instance Memoizable Bool

data MemoStore = MemoStore
  { msDivisors :: IORef (IntMap.IntMap [Int])
  , msPrimeFactors :: IORef (IntMap.IntMap [Int])
  , msPrimeFactorization :: IORef (IntMap.IntMap [(Int, Int)])
  , msIsPrime :: IORef (IntMap.IntMap Bool)
  , msStats :: IORef CacheStats
  }

newMemoStore :: IO MemoStore
newMemoStore = do
  divisorsCache <- newIORef IntMap.empty
  primeFactorsCache <- newIORef IntMap.empty
  primeFactorizationCache <- newIORef IntMap.empty
  isPrimeCache <- newIORef IntMap.empty
  statsRef <- newIORef (CacheStats 0 0 0)
  pure MemoStore
    { msDivisors = divisorsCache
    , msPrimeFactors = primeFactorsCache
    , msPrimeFactorization = primeFactorizationCache
    , msIsPrime = isPrimeCache
    , msStats = statsRef
    }

-- Backwards-compatible global store
-- SAFETY: NOINLINE ensures single initialization; see module header for unsafePerformIO safety argument
{-# NOINLINE globalMemoStore #-}
globalMemoStore :: MemoStore
globalMemoStore = unsafePerformIO newMemoStore

-- | Memoize a pure function with Int keys using thread-safe global cache.
-- SAFETY: unsafePerformIO is safe here because:
--   - The function 'f' is pure (deterministic, no side effects)
--   - atomicModifyIORef' ensures thread-safe cache access
--   - The result is the same whether cached or computed
{-# INLINE memoizeInt #-}
{-# SPECIALIZE memoizeInt ::
      IORef (IntMap.IntMap [Int])
      -> IORef CacheStats
      -> (Int -> [Int])
      -> Int
      -> [Int]
  #-}
{-# SPECIALIZE memoizeInt ::
      IORef (IntMap.IntMap [(Int, Int)])
      -> IORef CacheStats
      -> (Int -> [(Int, Int)])
      -> Int
      -> [(Int, Int)]
  #-}
{-# SPECIALIZE memoizeInt ::
      IORef (IntMap.IntMap Bool)
      -> IORef CacheStats
      -> (Int -> Bool)
      -> Int
      -> Bool
  #-}
memoizeInt :: Memoizable b => IORef (IntMap.IntMap b) -> IORef CacheStats -> (Int -> b) -> Int -> b
memoizeInt cacheRef statsRef f x = unsafePerformIO $ do
  -- Atomic lookup-or-insert: check cache, compute if missing
  (result, isHit) <- atomicModifyIORef' cacheRef $ \cache ->
    case IntMap.lookup x cache of
      Just val -> (cache, (val, True))
      Nothing ->
        let !computed = f x
         in (IntMap.insert x computed cache, (computed, False))
  -- Update stats based on hit/miss
  atomicModifyIORef' statsRef $ \s ->
    if isHit
      then (s { csHits = csHits s + 1 }, ())
      else (s { csMisses = csMisses s + 1, csCacheSize = csCacheSize s + 1 }, ())
  return result

-- Memoized versions of number theory functions

divisorsMemo :: Int -> [Int]
{-# INLINE divisorsMemo #-}
divisorsMemo = divisorsMemoWith globalMemoStore

primeFactorsMemo :: Int -> [Int]
{-# INLINE primeFactorsMemo #-}
primeFactorsMemo = primeFactorsMemoWith globalMemoStore

primeFactorizationMemo :: Int -> [(Int, Int)]
{-# INLINE primeFactorizationMemo #-}
primeFactorizationMemo = primeFactorizationMemoWith globalMemoStore

isPrimeMemo :: Int -> Bool
{-# INLINE isPrimeMemo #-}
isPrimeMemo = isPrimeMemoWith globalMemoStore

divisorsMemoWith :: MemoStore -> Int -> [Int]
divisorsMemoWith store = memoizeInt (msDivisors store) (msStats store) divisors

primeFactorsMemoWith :: MemoStore -> Int -> [Int]
primeFactorsMemoWith store = memoizeInt (msPrimeFactors store) (msStats store) primeFactors

primeFactorizationMemoWith :: MemoStore -> Int -> [(Int, Int)]
primeFactorizationMemoWith store = memoizeInt (msPrimeFactorization store) (msStats store) primeFactorization

isPrimeMemoWith :: MemoStore -> Int -> Bool
isPrimeMemoWith store = memoizeInt (msIsPrime store) (msStats store) isPrime

-- Derived memoized functions that use the cached primitives

numSylowMemo :: Int -> Int -> [Int]
{-# INLINE numSylowMemo #-}
numSylowMemo = numSylowMemoWith globalMemoStore

pKillableMemo :: Int -> Int -> Bool
{-# INLINE pKillableMemo #-}
pKillableMemo = pKillableMemoWith globalMemoStore

sylowKillableMemo :: Int -> Bool
{-# INLINE sylowKillableMemo #-}
sylowKillableMemo = sylowKillableMemoWith globalMemoStore

numSylowMemoWith :: MemoStore -> Int -> Int -> [Int]
numSylowMemoWith store p n = [d | d <- divisorsMemoWith store n, d `mod` p == 1]

pKillableMemoWith :: MemoStore -> Int -> Int -> Bool
pKillableMemoWith store p n = all (\d -> d == 1 || d `mod` p /= 1) (divisorsMemoWith store n)

sylowKillableMemoWith :: MemoStore -> Int -> Bool
sylowKillableMemoWith _ 1 = True
sylowKillableMemoWith store n =
  let ps = reverse (primeFactorsMemoWith store n)
   in any (\p -> pKillableMemoWith store p n) ps

-- Cache statistics functions

getCacheStats :: IO CacheStats
getCacheStats = getCacheStatsWith globalMemoStore

resetCacheStats :: IO ()
resetCacheStats = resetCacheStatsWith globalMemoStore

getCacheStatsWith :: MemoStore -> IO CacheStats
getCacheStatsWith store = readIORef (msStats store)

resetCacheStatsWith :: MemoStore -> IO ()
resetCacheStatsWith store = do
  writeIORef (msDivisors store) IntMap.empty
  writeIORef (msPrimeFactors store) IntMap.empty
  writeIORef (msPrimeFactorization store) IntMap.empty
  writeIORef (msIsPrime store) IntMap.empty
  writeIORef (msStats store) (CacheStats 0 0 0)
