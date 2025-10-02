-- | Proof reconstruction and pretty printing
{-# LANGUAGE RecordWildCards #-}
module ProofPrinter where

import qualified Data.Map.Strict as M
import qualified Data.Set as S
import Data.List (intercalate)
import Data.Maybe (fromMaybe)

import Types

-- | Helper function for cartesian product  
cartesian :: [[a]] -> [[a]]
cartesian [] = [[]]
cartesian (xs:xss) = [x:ys | x <- xs, ys <- cartesian xss]

-- | Pretty print a fact
prettyFact :: Fact -> String
prettyFact (Fact name args _ _) = name ++ "(" ++ intercalate ", " args ++ ")"

-- | Pretty print a substitution
prettySubst :: Subst -> String
prettySubst subst = 
  let bindings = M.toList subst
  in if null bindings 
     then ""
     else " {" ++ intercalate ", " [var ++ " := " ++ val | (var, val) <- bindings] ++ "}"

-- | Find all facts that are instances of the goal
findGoalInstances :: Env -> Fact -> [Fact]
findGoalInstances Env{..} goal =
  [f | f <- S.toList eFacts, 
       fName f == fName goal, 
       fArgs f == fArgs goal]

-- | Extract proof tree for a specific fact
data ProofNode = ProofNode
  { pnFact :: Fact
  , pnProvenance :: Maybe Provenance
  , pnParents :: [ProofNode]
  , pnDepth :: Int
  } deriving (Show)

-- | Build proof tree for a fact
buildProofTree :: Env -> Fact -> Int -> ProofNode
buildProofTree env fact maxDepth
  | maxDepth <= 0 = ProofNode fact (fProv fact) [] 0
  | otherwise = case fProv fact of
      Nothing -> ProofNode fact Nothing [] 0
      Just ProvHypothesis -> ProofNode fact (Just ProvHypothesis) [] 0
      Just prov@ProvTheorem{..} -> 
        let parentTrees = map (\p -> buildProofTree env p (maxDepth - 1)) parentFacts
            depth = 1 + maximum (0 : map pnDepth parentTrees)
        in ProofNode fact (Just prov) parentTrees depth

-- | Pretty print a proof tree
prettyProofTree :: ProofNode -> [String]
prettyProofTree = prettyProofTree' 0
  where
    prettyProofTree' indent (ProofNode fact prov parents _) =
      let prefix = replicate (indent * 2) ' '
          factStr = prefix ++ "• " ++ prettyFact fact
          provStr = case prov of
            Nothing -> prefix ++ "  (no provenance)"
            Just ProvHypothesis -> prefix ++ "  (hypothesis)"
            Just ProvTheorem{..} -> 
              prefix ++ "  by " ++ thmName ++ 
              (case provSubs of
                 Just subs -> prettySubst subs
                 Nothing -> "")
          parentLines = concatMap (prettyProofTree' (indent + 1)) parents
      in factStr : provStr : parentLines

-- | Find minimal proof for goal
findMinimalProof :: Env -> Fact -> Maybe ProofNode
findMinimalProof env goal =
  let instances = findGoalInstances env goal
      trees = map (\inst -> buildProofTree env inst 10) instances
      -- Pick the tree with smallest depth
      minTree = case trees of
        [] -> Nothing
        ts -> Just $ minimumBy (\a b -> compare (pnDepth a) (pnDepth b)) ts
  in minTree
  where
    minimumBy f (x:xs) = foldl (\acc y -> if f y acc == LT then y else acc) x xs
    minimumBy _ [] = error "minimumBy: empty list"

-- | Print complete proof
printProof :: Env -> Fact -> IO ()
printProof env goal = do
  case findMinimalProof env goal of
    Nothing -> putStrLn "No proof found for goal."
    Just proofTree -> do
      putStrLn "\n=== PROOF ==="
      putStrLn $ "Goal: " ++ prettyFact goal
      putStrLn ""
      mapM_ putStrLn (prettyProofTree proofTree)
      putStrLn "=== END PROOF ==="

-- | Print proof with disjunction case analysis
printProofWithCases :: Env -> Fact -> IO ()
printProofWithCases env goal = do
  let instances = findGoalInstances env goal
  
  if null instances
    then putStrLn "No proof found for goal."
    else do
      putStrLn "\n=== PROOF ==="
      putStrLn $ "Goal: " ++ prettyFact goal
      putStrLn ""
      
      -- Check if this is a direct proof or requires case analysis
      let directProofs = filter (S.null . fDeps) instances
      
      if not (null directProofs)
        then do
          putStrLn "Direct proof:"
          case findMinimalProof env goal of
            Just tree -> mapM_ putStrLn (prettyProofTree tree)
            Nothing -> putStrLn "Error: could not reconstruct proof tree"
        else do
          putStrLn "Proof by case analysis on disjunctions:"
          printCaseAnalysis env instances
      
      putStrLn "=== END PROOF ==="

-- | Print detailed case analysis showing how each branch closes
printCaseAnalysis :: Env -> [Fact] -> IO ()
printCaseAnalysis env@Env{..} instances = do
  let allDeps = S.unions (map fDeps instances)
      disjIds = S.toList (S.map fst allDeps)
      arities = [(did, length (case M.lookup did eDisjs of
                                 Just disj -> dAlts disj
                                 Nothing -> [])) 
                | did <- disjIds]
      
  putStrLn $ "Analyzing " ++ show (length disjIds) ++ " disjunctions:"
  
  -- First show the disjunctions
  mapM_ printDisjunction disjIds
  
  -- Then show detailed case analysis
  putStrLn "\nDetailed case analysis:"
  if length disjIds <= 3  -- Only for manageable number of disjunctions
    then do
      let assignments = cartesian [[i | i <- [0..arity-1]] | (_, arity) <- arities]
          disjIdsList = map fst arities
      putStrLn $ "Checking " ++ show (length assignments) ++ " case combinations:"
      mapM_ (printCaseResolution env disjIdsList) (zip [1..] assignments)
    else putStrLn "Too many disjunctions for detailed case analysis."
  
  where
    printDisjunction did = case M.lookup did eDisjs of
      Nothing -> putStrLn $ "  Disjunction " ++ show did ++ ": (not found)"
      Just Disj{..} -> do
        putStrLn $ "  " ++ fromMaybe ("Disjunction " ++ show did) dLabel ++ ":"
        case dProv of
          Just ProvTheorem{..} -> do
            putStrLn $ "    Generated by: " ++ thmName
            putStrLn $ "    From: " ++ intercalate " ∧ " (map prettyFact parentFacts)
          _ -> return ()
        putStrLn "    Cases:"
        mapM_ (\(i, alt) -> putStrLn $ "      [" ++ show i ++ "] " ++ prettyFact alt) 
              (zip [0..] dAlts)

-- | Print how a specific case assignment resolves
printCaseResolution :: Env -> [Int] -> (Int, [Int]) -> IO ()
printCaseResolution Env{..} disjIds (caseNum, assignment) = do
  let assignSet = S.fromList (zip disjIds assignment)
      caseLabels = [getCaseLabel did idx | (did, idx) <- zip disjIds assignment]
      validFacts = [f | f <- S.toList eFacts, 
                       fDeps f `S.isSubsetOf` assignSet]
      contradictions = [f | f <- validFacts, fName f == "false"]
  
  putStrLn $ "  Case " ++ show caseNum ++ ": " ++ intercalate ", " caseLabels
  
  if not (null contradictions)
    then do
      let contradiction = head contradictions
      putStrLn $ "    → CONTRADICTION: " ++ prettyFact contradiction
      case fProv contradiction of
        Just prov -> putStrLn $ "    → Derived by: " ++ provToString prov
        Nothing -> putStrLn $ "    → (no provenance)"
    else putStrLn $ "    → No direct contradiction found"
  
  where
    getCaseLabel did idx = case M.lookup did eDisjs of
      Just disj -> if idx < length (dAlts disj)
                   then prettyFact (dAlts disj !! idx)
                   else "case_" ++ show idx
      Nothing -> "unknown"
    
    provToString ProvHypothesis = "hypothesis"
    provToString ProvTheorem{..} = thmName ++ " applied to " ++ 
                                  intercalate ", " (map prettyFact parentFacts)

-- | Summary of proof statistics
printProofStats :: Env -> IO ()
printProofStats Env{..} = do
  putStrLn "\n=== PROOF STATISTICS ==="
  putStrLn $ "Total facts: " ++ show (S.size eFacts)
  putStrLn $ "Total disjunctions: " ++ show (M.size eDisjs)
  
  let factsByTheorem = M.fromListWith (+) 
        [(case fProv f of
            Just ProvTheorem{..} -> thmName
            Just ProvHypothesis -> "hypothesis"  
            Nothing -> "unknown", 1) 
        | f <- S.toList eFacts]
  
  putStrLn "Facts by source:"
  mapM_ (\(source, count) -> putStrLn $ "  " ++ source ++ ": " ++ show count)
        (M.toList factsByTheorem)

-- | Interactive proof exploration
exploreProof :: Env -> Fact -> IO ()
exploreProof env goal = do
  putStrLn $ "\nExploring proof for: " ++ prettyFact goal
  putStrLn "Commands: [p]roof, [s]tats, [c]ases, [q]uit"
  
  let loop = do
        putStr "> "
        cmd <- getLine
        case cmd of
          "p" -> printProof env goal >> loop
          "s" -> printProofStats env >> loop  
          "c" -> printProofWithCases env goal >> loop
          "q" -> putStrLn "Done."
          "" -> loop
          _ -> putStrLn "Unknown command" >> loop
  
  loop