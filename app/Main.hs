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
        os -> do
          results <- mapM (runOrder cfg) os
          let validResults = [r | Just r <- results]
              invalidCount = length [() | Nothing <- results]
              successCount = length (filter id validResults)
              failCount = length validResults - successCount
          putStrLn ""
          putStrLn $ "Summary: processed=" ++ show (length validResults)
            ++ ", success=" ++ show successCount
            ++ ", failure=" ++ show failCount
            ++ ", invalid=" ++ show invalidCount
  where
    interactiveLoop cfg = do
      putStr "Enter a positive group order (blank to quit): "
      hFlush stdout
      line <- getLine
      if null line
        then pure ()
        else do
          _ <- runOrder cfg line
          interactiveLoop cfg

    runOrder cfg line =
      case parsePositiveOrder line of
        Right n -> do
          let initialFacts = [group (sym "G"), order (sym "G") (num n), simple (sym "G")]
              goal = falseFact
              env = initEnv initialFacts thmList thmNames goal
          success <- autoSolveWith cfg env
          pure (Just success)
        Left err -> do
          putStrLn $ "Invalid order: " ++ line ++ " (" ++ err ++ ")"
          pure Nothing

    parsePositiveOrder :: String -> Either String Int
    parsePositiveOrder raw =
      case readMaybe raw :: Maybe Int of
        Nothing -> Left "not an integer"
        Just n
          | n <= 0 -> Left "must be positive"
          | otherwise -> Right n

    parseArgs :: [String] -> Either String (SolverConfig, [String])
    parseArgs = go defaultConfig []
      where
        go cfg acc [] = Right (cfg, reverse acc)
        go _ _ ("--help" : _) = Left usageText
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

    usageText =
      unlines
        [ "Usage: sylow-solver [--order N | N] [--max-iterations K] [--batch-size K] [--verbose]"
        , "       Output modes: --clean (default), --classic, --tree"
        , "       Orders must be positive integers."
        , "Note: a simple group of order 60 exists (A5), so contradiction is not expected in general for |G|=60."
        ]
