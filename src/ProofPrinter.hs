-- | Proof reconstruction and pretty printing
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
          -- Always print full case analysis without short-circuiting
          let instances' = map (dedupFactDeps env) instances
          putStrLn "Proof by case analysis on disjunctions:"
          printCaseAnalysis env instances'
      
      putStrLn "=== END PROOF ==="

-- | Estimate number of case combinations from goal instances
estimateCombos :: Env -> [Fact] -> (Int, Int)
estimateCombos Env{..} instances =
  let allDeps = S.unions (map fDeps instances)
      disjIds = S.toList (S.map fst allDeps)
      arities = [ length (case M.lookup did eDisjs of
                             Just disj -> dAlts disj
                             Nothing -> [])
                | did <- disjIds]
      combos = product (map (max 1) arities)
  in (combos, length disjIds)

-- | Choose one contradiction instance and its assignment for printing a concrete proof
pickBestContradiction :: Env -> [Fact] -> Maybe (Fact, S.Set Dep, [String])
pickBestContradiction env@Env{..} instances =
  let withDeps = [(f, fDeps f) | f <- instances]
      -- Heuristic: prefer proofs that mention embedding/alternating, then fewer disjunctions, then smaller depth
      hasEmbed t =
        let node = buildProofTree env t 10
            mentionsEmbeds = containsName node (\n -> n == "embedsInSym" || n == "alternatingGroup")
        in if mentionsEmbeds then 0 else 1  -- lower is better
      containsName (ProofNode (Fact nm _ _ _) _ parents _) p =
        p nm || any (\ch -> containsName ch p) parents
      scored = [ (f, deps, hasEmbed f, S.size deps, pnDepth (buildProofTree env f 10))
               | (f, deps) <- withDeps]
      cmp ( _, _, e1, k1, d1) ( _, _, e2, k2, d2) = compare e1 e2 <> compare k1 k2 <> compare d1 d2
  in case sortByMaybe cmp scored of
       [] -> Nothing
       ((f, deps, _, _, _):_) ->
         let labels = depsToLabels env (S.toList deps)
         in Just (f, deps, labels)

-- | Convert dependency set to human-readable case labels
depsToLabels :: Env -> [Dep] -> [String]
depsToLabels Env{..} deps =
  [ case M.lookup did eDisjs of
      Just disj | idx < length (dAlts disj) -> prettyFact (dAlts disj !! idx)
      _ -> "case_" ++ show idx
  | (did, idx) <- deps]

-- | Utility: sort a list by a comparator, safely returning [] on empty
sortByMaybe :: (a -> a -> Ordering) -> [a] -> [a]
sortByMaybe cmp xs =
  let go [] = []
      go (y:ys) = foldl ins [y] ys
      ins acc z = insertByCmp z acc
      insertByCmp z [] = [z]
      insertByCmp z (a:as) = case cmp z a of
        LT -> z:a:as
        _  -> a : insertByCmp z as
  in go xs

-- | Print detailed case analysis showing how each branch closes
printCaseAnalysis :: Env -> [Fact] -> IO ()
printCaseAnalysis env@Env{..} instances = do
  let allDeps = S.unions (map fDeps instances)
      disjIdsRaw = S.toList (S.map fst allDeps)
      disjIds = dedupDisjunctions env disjIdsRaw
      arities = [(did, length (case M.lookup did eDisjs of
                                 Just disj -> dAlts disj
                                 Nothing -> [])) 
                | did <- disjIds]
      totalCombos = product [arity | (_, arity) <- arities]
      maxCombosToPrint = 1024  -- prevent explosion
      
  putStrLn $ "Analyzing " ++ show (length disjIds) ++ " disjunctions:"
  
  -- First show the disjunctions
  mapM_ printDisjunction disjIds
  
  -- Then show detailed case analysis (always enumerate all combinations)
  putStrLn "\nDetailed case analysis:"
  let assignments = cartesian [[i | i <- [0..arity-1]] | (_, arity) <- arities]
      disjIdsList = map fst arities
  putStrLn $ "Checking " ++ show (length assignments) ++ " case combinations:"
  mapM_ (printCaseResolution env disjIdsList) (zip [1..] assignments)
  
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
      -- Prefer contradictions that involve embeddings/alternating in their derivation
      scoreContr f =
        let tree = buildProofTree Env{..} f 12
            mentionsEmbed = containsName tree (\nm -> nm == "embedsInSym" || nm == "alternatingGroup")
            topName = case fProv f of
                        Just ProvTheorem{..} -> thmName
                        _ -> ""
            prefersTop = if topName == "OrderMustDivideSym" || topName == "OrderMustDivideAlt" then 0 else 1
            depth = pnDepth tree
        in (if mentionsEmbed then 0 else 1, prefersTop, depth)
      containsName (ProofNode (Fact nm _ _ _) _ parents _) p =
        p nm || any (\ch -> containsName ch p) parents
      bestContr = case contradictions of
                    [] -> Nothing
                    cs -> Just $ snd $ minimumByCmp compare (map (\c -> (scoreContr c, c)) cs)
  
  putStrLn $ "  Case " ++ show caseNum ++ ": " ++ intercalate ", " caseLabels
  
  if maybe False (const True) bestContr
    then do
      let contradiction = fromMaybe (head contradictions) bestContr
      putStrLn $ "    → CONTRADICTION: " ++ prettyFact contradiction
      -- Print full derivation for this case
      mapM_ putStrLn $ map ("    " ++) (prettyProofTree (buildProofTree Env{..} contradiction 12))
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
    minimumByCmp cmpf (x:xs) = foldl (\acc y -> if cmpf (fst y) (fst acc) == LT then y else acc) x xs
    minimumByCmp _ [] = error "minimumByCmp: empty list"

-- Deduplicate identical disjunctions by structure (name and args of alts)
dedupDisjunctions :: Env -> [Int] -> [Int]
dedupDisjunctions Env{..} dids =
  let keyOf did = case M.lookup did eDisjs of
        Just Disj{..} -> Just (map (\(Fact nm as _ _) -> (nm, as)) dAlts)
        Nothing -> Nothing
      go acc seenKeys [] = reverse acc
      go acc (seenKeys :: S.Set [(String,[String])]) (d:ds) =
        case keyOf d of
          Just k -> if S.member k seenKeys
                    then go acc seenKeys ds
                    else go (d:acc) (S.insert k seenKeys) ds
          Nothing -> go acc seenKeys ds
  in go [] (S.fromList []) dids

-- Remove duplicate disjunction dependencies from a fact (by identical disjunction key)
dedupFactDeps :: Env -> Fact -> Fact
dedupFactDeps env@Env{..} f@Fact{..} =
  let deps = S.toList fDeps
      -- keep smallest did for identical disjunctions
      grouped = M.fromListWith min
        [ (key, did)
        | (did, idx) <- deps
        , let key = case M.lookup did eDisjs of
                       Just Disj{..} -> Just (map (\(Fact nm as _ _) -> (nm, as)) dAlts)
                       Nothing -> Nothing
        ]
      didsToKeep = S.fromList (M.elems grouped)
      newDeps = S.fromList [ (did, idx) | (did, idx) <- deps, S.member did didsToKeep ]
  in f { fDeps = newDeps }

-- Pick any easy terminal contradictions and return its labels
-- Easy terminals for this problem family: n2=1, n3=1, n2=3, n3=4
pickEasyTerminal :: Env -> [Fact] -> Maybe (Fact, [String])
pickEasyTerminal env@Env{..} instances =
  let instances' = map (dedupFactDeps env) instances
      withDeps = [ (f, depsToLabels env (S.toList (fDeps f))) | f <- instances']
      easy f labels = any (\s ->
                           s == "numSylow(2, G, 1)" ||
                           s == "numSylow(3, G, 1)" ||
                           s == "numSylow(2, G, 3)" ||
                           s == "numSylow(3, G, 4)") labels
  in case [ (f, labels) | (f, labels) <- withDeps, easy f labels ] of
       ((f, labels):_) -> Just (f, labels)
       _ -> Nothing

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