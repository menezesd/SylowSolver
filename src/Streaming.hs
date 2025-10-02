-- | Streaming and lazy evaluation for large proof search spaces
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
module Streaming where

import Control.Monad.State.Strict
import Control.Monad.Except
import Control.Monad (mapM)
import qualified Data.Set as S
import Data.List (unfoldr)

import Types
import Errors
import PureProver
import Matching

-- | Lazy stream of theorem applications
data Stream a = Stream a (Stream a) | EmptyStream

instance Functor Stream where
  fmap f (Stream x xs) = Stream (f x) (fmap f xs)
  fmap _ EmptyStream = EmptyStream

-- | Take n elements from a stream
takeStream :: Int -> Stream a -> [a]
takeStream 0 _ = []
takeStream _ EmptyStream = []
takeStream n (Stream x xs) = x : takeStream (n-1) xs

-- | Filter a stream lazily
filterStream :: (a -> Bool) -> Stream a -> Stream a
filterStream p (Stream x xs)
  | p x = Stream x (filterStream p xs)
  | otherwise = filterStream p xs
filterStream _ EmptyStream = EmptyStream

-- | Interleave two streams for fair enumeration
interleaveStream :: Stream a -> Stream a -> Stream a
interleaveStream (Stream x xs) ys = Stream x (interleaveStream ys xs)
interleaveStream EmptyStream ys = ys

-- | Convert list to stream
listToStream :: [a] -> Stream a
listToStream [] = EmptyStream
listToStream (x:xs) = Stream x (listToStream xs)

-- | Simple lazy fact tuple generation
lazyFactTuples :: Int -> [Fact] -> [[Fact]]
lazyFactTuples 0 _ = [[]]
lazyFactTuples 1 facts = map (:[]) facts
lazyFactTuples k facts = [f:rest | f <- facts, rest <- lazyFactTuples (k-1) facts]

-- | Streaming theorem application with resource limits
data StreamConfig = StreamConfig
  { maxTuples :: Int        -- Maximum tuples to try per theorem
  , maxDepth :: Int         -- Maximum search depth
  , chunkSize :: Int        -- Process in chunks for memory efficiency
  } deriving (Show)

defaultStreamConfig :: StreamConfig
defaultStreamConfig = StreamConfig 1000 1000 1000

-- | Apply theorems with limited search
streamTheoremApplications :: StreamConfig -> [Theorem] -> [Fact] -> [(String, ThmOut, S.Set Dep, [Fact], Subst)]
streamTheoremApplications config theorems facts = 
  concatMap (streamSingleTheorem config facts) theorems

-- | Stream applications for a single theorem  
streamSingleTheorem :: StreamConfig -> [Fact] -> Theorem -> [(String, ThmOut, S.Set Dep, [Fact], Subst)]
streamSingleTheorem StreamConfig{..} facts theorem@Theorem{..} =
  let candidateTuples = take maxTuples $ generateTuplesForTemplate facts (tTemplate)
      
      tryApply tuple = case matchTemplate tuple tTemplate of
        Right substitution -> 
          let parentDeps = S.unions (map fDeps tuple)
              outputs = tApply tuple
          in Right [(tName, output, parentDeps, tuple, substitution) | output <- outputs]
        Left _ -> Left []
      
      successfulApplications = concat [results | tuple <- candidateTuples,
                                                 let res = tryApply tuple,
                                                 case res of { Right _ -> True; Left _ -> False },
                                                 let Right results = res]
  in successfulApplications

-- | Chunked processing for memory efficiency
processInChunks :: StreamConfig -> [a] -> (a -> ProverM b) -> ProverM [b]
processInChunks StreamConfig{..} items processor =
  mapM processor (take (maxDepth * chunkSize) items)

-- | Lazy proof search with streaming
streamingProofSearch :: StreamConfig -> [Theorem] -> Fact -> ProverM Bool
streamingProofSearch config theorems goal = do
  searchWithLimit (maxDepth config)
  where
    searchWithLimit 0 = throwError $ TimeoutError (maxDepth config)
    searchWithLimit depth = do
      env <- get
      let facts = S.toList (eFacts env)
          applications = streamTheoremApplications config theorems facts
      
      -- Process applications
      results <- processInChunks config applications processApplication
      
      -- Check if goal is proven
      proven <- checkGoalProven goal
      if proven
        then return True
        else if null results  -- No more applications possible
          then return False
          else searchWithLimit (depth - 1)
    
    processApplication (thmName, output, deps, parents, subst) = do
      processTheoremOutput thmName output deps parents subst
      return True

-- | Memory-efficient fact enumeration
-- Uses generators to avoid holding all combinations in memory
factEnumerator :: [Fact] -> Int -> [Fact] -> [[Fact]]
factEnumerator facts 0 acc = [reverse acc]
factEnumerator [] _ _ = []
factEnumerator (f:fs) k acc = 
  factEnumerator fs k (f:acc) ++ factEnumerator fs (k-1) acc

-- | Bounded depth-first search with lazy evaluation
boundedDFS :: Int -> [Theorem] -> ProverM Bool
boundedDFS maxDepth theorems = searchDFS maxDepth
  where
    searchDFS 0 = return False
    searchDFS depth = do
      env <- get
      let facts = S.toList (eFacts env)
      
      -- Try each theorem lazily
      success <- tryTheorems theorems facts
      if success
        then return True
        else searchDFS (depth - 1)
    
    tryTheorems [] _ = return False
    tryTheorems (thm:thms) facts = do
      applied <- tryApplyTheorem thm facts
      if applied
        then return True
        else tryTheorems thms facts
    
    tryApplyTheorem theorem@Theorem{..} facts = do
      let Template patterns = tTemplate
          tupleSize = length patterns
          -- Generate tuples lazily using orderedTuples from PureProver  
          tuples = orderedTuples tupleSize facts
      
      tryTuples tuples
      where
        tryTuples [] = return False
        tryTuples (tuple:rest) = do
          case matchTemplate tuple tTemplate of
            Right subst -> do
              let outputs = tApply tuple
                  parentDeps = S.unions (map fDeps tuple)
              mapM_ (\out -> processTheoremOutput tName out parentDeps tuple subst) outputs
              return True
            Left _ -> tryTuples rest