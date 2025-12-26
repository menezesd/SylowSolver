{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Auto
import Core
import Environment.Init (initEnv)
import Predicates
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)
import Theorems

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    Left err -> putStrLn err
    Right (cfg, orders) ->
      case orders of
        [] -> interactiveLoop cfg
        os -> mapM_ (runOrder cfg) os
  where
    interactiveLoop cfg = do
      putStr "Enter a group order (blank to quit): "
      hFlush stdout
      line <- getLine
      if null line
        then pure ()
        else do
          runOrder cfg line
          interactiveLoop cfg

    runOrder cfg line =
      case readMaybe line :: Maybe Int of
        Just n -> do
          let initialFacts = [group (sym "G"), order (sym "G") (num n), simple (sym "G")]
              goal = falseFact
              env = initEnv initialFacts thmList thmNames goal
          _ <- autoSolveWith cfg env
          pure ()
        Nothing -> do
          putStrLn $ "Invalid order (not an integer): " ++ line

    parseArgs :: [String] -> Either String (SolverConfig, [String])
    parseArgs = go defaultConfig []
      where
        go cfg acc [] = Right (cfg, reverse acc)
        go cfg acc ("--max-iterations" : n : rest) =
          case readMaybe n of
            Just i -> go cfg { scMaxIterations = i } acc rest
            Nothing -> Left $ "Invalid --max-iterations: " ++ n
        go cfg acc ("--batch-size" : n : rest) =
          case readMaybe n of
            Just i -> go cfg { scBatchSize = i } acc rest
            Nothing -> Left $ "Invalid --batch-size: " ++ n
        go cfg acc ("--verbose" : rest) = go cfg { scVerbose = True } acc rest
        go cfg acc ("-v" : rest) = go cfg { scVerbose = True } acc rest
        go cfg acc ("--dump-hash-buckets" : rest) = go cfg { scDumpHashBuckets = True } acc rest
        go cfg acc ("--tree" : rest) = go cfg { scOutputMode = OutputTree } acc rest
        go cfg acc ("--classic" : rest) = go cfg { scOutputMode = OutputClassic } acc rest
        go cfg acc ("--clean" : rest) = go cfg { scOutputMode = OutputClean } acc rest
        go cfg acc ("--order" : n : rest) = go cfg (n : acc) rest
        go cfg acc (arg : rest)
          | Just (_ :: Int) <- readMaybe arg = go cfg (arg : acc) rest
          | otherwise = Left $ "Unrecognized argument: " ++ arg
