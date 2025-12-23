module EnvPrint
  ( printRelevantFacts
  , printProofTrace
  ) where

import Core
import Env
import ProofTrace

printRelevantFacts :: ProofEnvironment -> IO ()
printRelevantFacts = printProofTrace . buildTrace

printProofTrace :: [ProofStep] -> IO ()
printProofTrace = mapM_ printStep
  where
    printStep step
      | psUseful step = do
          putStrLn
            ( labelText (psLabel step)
                ++ " : "
                ++ factName (psFact step)
                ++ " "
                ++ show (map argText (factArgs (psFact step)))
            )
          case psConcThm step of
            Just thmName' ->
              putStrLn
                ( "    by thm "
                    ++ thmName'
                    ++ " applied to facts "
                    ++ unwords (map labelText (psDependencies step))
                )
            Nothing -> putStrLn "    by hypothesis"
          if null (psDisAncestors step)
            then pure ()
            else putStrLn ("    Disjunctions in history: " ++ show (map disjEntryText (psDisAncestors step)))
          putStrLn ""
      | otherwise = pure ()

disjEntryText :: (DisjId, Int) -> String
disjEntryText (DisjId n, idx) = "(" ++ "D" ++ show n ++ "," ++ show idx ++ ")"
