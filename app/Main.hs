module Main where

import Auto
import Core
import Env
import Predicates
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
import Text.Read (readMaybe)
import Theorems

main :: IO ()
main = do
  args <- getArgs
  case parseArgs args of
    [] -> interactiveLoop
    orders -> mapM_ runOrder orders
  where
    interactiveLoop = do
      putStr "Enter a group order (blank to quit): "
      hFlush stdout
      line <- getLine
      if null line
        then pure ()
        else do
          runOrder line
          interactiveLoop

    runOrder line =
      case readMaybe line :: Maybe Int of
        Just n -> do
          -- Use Num constructor for efficient numeric handling
          let facts = [group (sym "G"), order (sym "G") (num n), simple (sym "G")]
              goal = falseFact
              env = initEnv facts thmList thmNames goal
          _ <- autoSolve env
          pure ()
        Nothing -> do
          putStrLn $ "Invalid order (not an integer): " ++ line

    parseArgs [] = []
    parseArgs ("--order" : n : rest) = n : parseArgs rest
    parseArgs ("--order" : []) = []
    parseArgs (arg : rest) = arg : parseArgs rest
