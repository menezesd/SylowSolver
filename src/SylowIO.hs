-- | IO and user interface for the Sylow solver
{-# LANGUAGE RecordWildCards #-}
module SylowIO where

import Control.Monad (when)
import System.Environment (getArgs)
import System.IO (isEOF)
import qualified Data.Set as S

import Types
import Errors
import Prover -- Changed from PureProver
import Theorems
import Streaming
import ProofPrinter
import System.Environment (lookupEnv)
import DebugLog (setDebugEnabled)

import Control.Monad.RWS.Strict (runRWS)

-- | Configuration for the solver
data SolverConfig = SolverConfig
  { verbose :: Bool
  , solverMaxRounds :: Int
  , useStreaming :: Bool
  , streamConfig :: StreamConfig
  } deriving (Show)

defaultSolverConfig :: SolverConfig
defaultSolverConfig = SolverConfig False 100 True defaultStreamConfig

-- | Create hypotheses for testing simple groups
createHypotheses :: Integer -> [Fact]
createHypotheses n = 
  [ (mkFactP PGroup [Sym "G"]) { fProv = Just ProvHypothesis }
  , (mkFactP POrder [Sym "G", Nat n]) { fProv = Just ProvHypothesis }
  , (mkFactP PSimple [Sym "G"]) { fProv = Just ProvHypothesis }
  ]

-- | The goal fact (contradiction)
goalFalse :: Fact
goalFalse = mkFactP PFalse []

-- | Run a proof attempt with proper error handling
runProofAttempt :: SolverConfig -> Integer -> IO ()
runProofAttempt config@SolverConfig{..} n = do
  putStrLn $ "Attempting: no simple group of order " ++ show n
  -- Enable debug logging if verbose or env var SYLOW_DEBUG=true
  envDbg <- lookupEnv "SYLOW_DEBUG"
  let dbg = verbose || (envDbg == Just "true")
  setDebugEnabled dbg
  
  let hypotheses = createHypotheses n
      goal = goalFalse
      env0 = Env
        { eFacts = S.fromList hypotheses
        , eDisjs = mempty
        , eFrontier = S.fromList hypotheses
        , eAppQueue = mempty
        , eNextDid = 0
        , eFresh = 0
        , eClosedAlts = S.empty
        }
      ((), envWithQueue, initTrace) = runRWS initialPopulateQueue (Engine standardTheorems solverMaxRounds 0) env0
      (finalEnv, trace) = runProver (Engine standardTheorems solverMaxRounds 0) envWithQueue
      proofResult = 
        if any Prover.isContradiction (S.toList (eFacts finalEnv))
          then Right True
          else Right False
          
  -- Debug output
  when dbg $ do
    putStrLn $ "DEBUG: Initial trace events: " ++ show (length initTrace)
    mapM_ (putStrLn . ("INIT: " ++) . show) initTrace
    putStrLn $ "DEBUG: Main trace events: " ++ show (length trace)
    mapM_ (putStrLn . ("MAIN: " ++) . show) (take 20 trace) -- Limit to avoid spam
  case proofResult of
        Right True -> do
          putStrLn "✓ CONTRADICTION derived (goal proven)."
          
          -- Print the actual proof
          printProof finalEnv (head (filter Prover.isContradiction (S.toList (eFacts finalEnv))))
          
          when verbose $ do
            putStrLn $ "\nFinal environment has " ++ show (S.size (eFacts finalEnv)) ++ " facts"
            putStrLn $ "Generated " ++ show (length (eDisjs finalEnv)) ++ " disjunctions"
            -- printProofStats finalEnv -- This function might need updates
        
        Right False -> 
          putStrLn "✗ Could not derive contradiction."
        
        Left err -> do
          putStrLn $ "✗ Prover error: " ++ prettyError err
          when verbose $ putStrLn $ "Error details: " ++ show err

isContradiction :: Fact -> Bool
isContradiction (Fact (PFalse) _ _ _) = True
isContradiction _ = False

-- | Parse command line arguments
parseArgs :: [String] -> (SolverConfig, Maybe Integer)
parseArgs args = parseArgs' defaultSolverConfig args Nothing
  where
    parseArgs' config [] target = (config, target)
    parseArgs' config ("--verbose":rest) target = 
      parseArgs' config{verbose = True} rest target
    parseArgs' config ("--no-streaming":rest) target =
      parseArgs' config{useStreaming = False} rest target  
    parseArgs' config ("--max-rounds":nStr:rest) target =
      case safeRead nStr of
        Right n -> parseArgs' config{solverMaxRounds = n, streamConfig = (streamConfig config){maxDepth = n}} rest target
        Left _ -> parseArgs' config rest target
    parseArgs' config (nStr:rest) _ =
      case safeRead nStr of
        Right n -> parseArgs' config rest (Just n)
        Left _ -> parseArgs' config rest Nothing

-- | Interactive mode for testing multiple orders
interactiveMode :: SolverConfig -> IO ()
interactiveMode config = do
  putStrLn "Sylow Solver - Interactive Mode"
  putStrLn "Enter group orders to test (or 'quit' to exit):"
  loop
  where
    loop = do
      putStr "> "
      input <- getLine
      case input of
        "quit" -> putStrLn "Goodbye!"
        "q" -> putStrLn "Goodbye!"
        "" -> loop
        _ -> case safeRead input of
          Right n -> do
            runProofAttempt config n
            putStrLn ""
            loop
          Left _ -> do
            putStrLn $ "Invalid input: " ++ input
            loop

-- | Main entry point
main :: IO ()
main = do
  args <- getArgs
  let (config, maybeTarget) = parseArgs args
  -- Initialize debug flag from env (CLI overrides)
  envDbg <- lookupEnv "SYLOW_DEBUG"
  setDebugEnabled (verbose config || envDbg == Just "true")
  
  case maybeTarget of
    Just n -> runProofAttempt config n
    Nothing -> do
      -- Check for stdin input
      hasStdin <- isEOF
      if not hasStdin
        then do
          line <- getLine
          case safeRead line of
            Right n -> runProofAttempt config n
            Left _ -> putStrLn $ "Invalid input on stdin: " ++ line
        else do
          -- Default examples if no input provided
          putStrLn "Running default examples..."
          runProofAttempt config 40
          putStrLn ""
          runProofAttempt config 24
          putStrLn ""
          -- Enter interactive mode
          interactiveMode config

-- | Benchmark mode for testing performance
benchmarkMode :: SolverConfig -> [Integer] -> IO ()
benchmarkMode config orders = do
  putStrLn "Benchmarking mode:"
  mapM_ (benchmarkSingle config) orders
  where
    benchmarkSingle cfg n = do
      putStr $ "Order " ++ show n ++ ": "
      -- Here you could add timing logic
      runProofAttempt cfg{verbose = False} n

-- | Debug mode with detailed tracing
debugMode :: Integer -> IO ()
debugMode n = do
  let config = defaultSolverConfig { verbose = True, useStreaming = False }
  putStrLn $ "Debug mode for order " ++ show n
  runProofAttempt config n