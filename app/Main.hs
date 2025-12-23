module Main where

import Auto
import Core
import Env
import Predicates
import System.Environment (getArgs)
import System.IO (hFlush, stdout)
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

    runOrder line = do
      let facts = [group (sym "G"), order (sym "G") (sym line), simple (sym "G")]
          goal = falseFact
          env = initEnv facts thmList thmNames goal
      _ <- autoSolve env
      pure ()

    parseArgs [] = []
    parseArgs ("--order" : n : rest) = n : parseArgs rest
    parseArgs ("--order" : []) = []
    parseArgs (arg : rest) = arg : parseArgs rest
