module EnvPrint
  ( printRelevantFacts
  ) where

import Core
import Env
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

printRelevantFacts :: ProofEnvironment -> IO ()
printRelevantFacts env = mapM_ printFact (peOrderedFacts env)
  where
    printFact lbl =
      case Map.lookup lbl (peFactLabels env) of
        Just (LFactEntry fe)
          | feUseful fe -> do
              putStrLn (labelText lbl ++ " : " ++ factName (feFact fe) ++ " " ++ show (map argText (factArgs (feFact fe))))
              case feConcThm fe of
                Just thmName' ->
                  putStrLn ("    by thm " ++ thmName' ++ " applied to facts " ++ unwords (map labelText (feDependencies fe)))
                Nothing -> putStrLn "    by hypothesis"
              if Set.null (feDisAncestors fe)
                then pure ()
                else putStrLn ("    Disjunctions in history: " ++ show (map disjEntryText (Set.toList (feDisAncestors fe))))
              putStrLn ""
        _ -> pure ()

labelText :: Label -> String
labelText lbl =
  case lbl of
    LFact (FactId n) -> "F" ++ show n
    LDisj (DisjId n) -> "D" ++ show n

disjEntryText :: (DisjId, Int) -> String
disjEntryText (DisjId n, idx) = "(" ++ "D" ++ show n ++ "," ++ show idx ++ ")"
