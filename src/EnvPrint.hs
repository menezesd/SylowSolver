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
          [ show step
          , case psConcThm step of
              Just thmName' ->
                ( "    by thm "
                    ++ theoremNameText thmName'
                    ++ " applied to facts "
                    ++ unwords (map labelText (psDependencies step))
                )
              Nothing -> "    by hypothesis"
          ]
            ++ if null (psDisAncestors step)
              then []
              else ["    Disjunctions in history: " ++ show (map disjAncText (psDisAncestors step))]
            ++ [""]
      | otherwise = []

disjAncText :: (DisjId, Int) -> String
disjAncText (DisjId n, idx) = "(" ++ "D" ++ show n ++ "," ++ show idx ++ ")"
