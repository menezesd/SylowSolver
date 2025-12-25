module EnvPrint
  ( printRelevantFacts
  , showProofTrace
  ) where

import Core
import Env
import ProofTrace

printRelevantFacts :: ProofEnvironment -> [String]
printRelevantFacts = showProofTrace . buildTrace

showProofTrace :: [ProofStep] -> [String]
showProofTrace = concatMap showStep
  where
    showStep step
      | psUseful step =
          [ ( labelText (psLabel step)
                ++ " : "
                ++ factName (psFact step)
                ++ " "
                ++ show (map argText (factArgs (psFact step)))
            )
          , case psConcThm step of
              Just thmName' ->
                ( "    by thm "
                    ++ thmName'
                    ++ " applied to facts "
                    ++ unwords (map labelText (psDependencies step))
                )
              Nothing -> "    by hypothesis"
          ]
            ++ if null (psDisAncestors step)
              then []
              else ["    Disjunctions in history: " ++ show (map disjEntryText (psDisAncestors step))]
            ++ [""]
      | otherwise = []

disjEntryText :: (DisjId, Int) -> String
disjEntryText (DisjId n, idx) = "(" ++ "D" ++ show n ++ "," ++ show idx ++ ")"
