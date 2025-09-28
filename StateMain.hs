-- | StateMain.hs
--
-- Main executable using the State monad-based proof environment.
-- Demonstrates cleaner, more composable code with monadic state management.

module Main where

import Core
import StateEnvironment  
import Auto
import qualified NumberTheory as NT
import qualified Data.Set as Set
import Text.Read (readMaybe)
import Control.Monad (when, unless)
import Control.Monad.State.Strict
import Data.Maybe (catMaybes, fromMaybe)
import Data.List (intercalate, nub, sort)
import qualified Data.Map.Strict as M

-- | Format a fact for human-readable display with branch context (unchanged)
formatFact :: Fact -> String
formatFact fact = formatFactWithContext fact ""

-- | Format a fact with explicit branch context prefix (unchanged)
formatFactWithContext :: Fact -> String -> String
formatFactWithContext fact contextPrefix = 
  let name = factName fact
      args = factArgs fact
      branchInfo = formatBranchContext fact
      factText = case (name, args) of
        ("group", [g]) -> g ++ " is a group"
        ("order", [g, n]) -> "order(" ++ g ++ ") = " ++ n
        ("sylow_p_subgroup", [h, p, g]) -> h ++ " is a " ++ p ++ "-Sylow subgroup of " ++ g
        ("sylow_order", [g, p, pk]) -> g ++ " has " ++ p ++ "-Sylow subgroups of order " ++ pk
        ("num_sylow", [p, g, n]) -> 
          if n == "1" 
            then g ++ " has a unique " ++ p ++ "-Sylow subgroup (therefore normal)"
            else g ++ " has exactly " ++ n ++ " " ++ p ++ "-Sylow subgroups"
        ("not_simple", [g]) -> "★ " ++ g ++ " is NOT SIMPLE"
        ("simple", [g]) -> g ++ " is simple"
        ("subgroup", [h, g]) -> h ++ " ⊆ " ++ g
        ("normal", [h, g]) -> h ++ " ⊴ " ++ g ++ " (normal subgroup)"
        ("more_than_one_sylow", [p, g]) -> "There are at least two " ++ p ++ "-Sylow subgroups in " ++ g
        ("max_sylow_intersection", [g, p, k]) -> "Among the " ++ p ++ "-Sylow subgroups of " ++ g ++ ", the largest pairwise intersection has size " ++ k
        ("divides", [m, n]) -> m ++ " | " ++ n
        ("false", []) -> "⊥ (contradiction reached)"
        ("alternating_group", [a, n]) -> a ++ " ≅ A_" ++ n ++ " (alternating group)"
        ("transitive_action", [g, n]) -> g ++ " acts transitively on " ++ n ++ " elements"
        ("order_pk_lower_bound", [g, p, n]) -> g ++ " has at least " ++ n ++ " elements of order divisible by " ++ p
        _ -> name ++ "(" ++ intercalate ", " args ++ ")"
  in contextPrefix ++ branchInfo ++ factText

-- | Format branch context for a fact (unchanged)
formatBranchContext :: Fact -> String
formatBranchContext fact =
  let ancestors = Set.toList (factDisAncestors fact)
      depth = factDepth fact
  in if null ancestors
     then ""  -- No branch context
     else 
       let branchLabels = map (\(label, idx) -> "Case " ++ label ++ "." ++ show (idx + 1)) ancestors
           branchStr = intercalate ", " branchLabels
           depthStr = if depth > 0 then "[depth " ++ show depth ++ "] " else ""
       in "[" ++ branchStr ++ "] " ++ depthStr

-- | Format a disjunction for human-readable display (unchanged)
formatDisjunction :: String -> [Fact] -> String  
formatDisjunction intro facts = 
  intro ++ " one of the following must hold:\\n" ++
  concatMap (\(i, fact) -> "    (" ++ show i ++ ") " ++ formatFact fact ++ "\n") 
            (zip [1 :: Int ..] facts) ++
  "    ┌─ Branching into " ++ show (length facts) ++ " cases..."

-- | Print a disjunction with a human-visible label and explicit case names (unchanged)
formatDisjunctionDetailed :: String -> Disjunction -> String
formatDisjunctionDetailed label disj =
  let facts = disjunctionFacts disj
      header = "Disjunction " ++ label ++ " (" ++ show (length facts) ++ " alternatives):\n"
      body = concatMap (\(i, f) -> "    (" ++ show (i+1) ++ ") " ++ formatFact f ++ "    [case: " ++ label ++ "." ++ show (i+1) ++ "]\n") (zip [0 :: Int ..] facts)
  in header ++ body

main :: IO ()
main = do
  putStrLn "=== Sylow Solver - State Monad Version ==="
  putStrLn ""
  
  -- Get group order from user
  putStrLn "Interactive Theorem Proving:"
  groupOrder <- getGroupOrderFromUser
  
  putStrLn $ "\nAnalyzing group of order " ++ show groupOrder ++ "..."
  putStrLn ""
  
  -- Analyze the group order
  analyzeGroupOrder groupOrder
  
  -- Set up the proof environment
  let
    g = "G"
    groupOrderStr = show groupOrder
    goalFact = false
    theorems = [ lagrange, simpleNotSimple ]
    initialFacts = [ group g, order g groupOrderStr, simple g ]
    hyperTheorems = [ sylowTheorem
          , singleSylowNotSimple
          , pGroupNotSimple
          , dividesContradiction
          , countOrderPkElements
          , countingContradiction
          , embedInAn
          , alternatingOrder
          , alternatingSimple
          , multipleSylows
          , possibleMaxIntersections
          , intersectionOfSylows
          , normalizerSylowIntersection
          , normalizerEverythingImpliesNormal
          , normalSubgroupToNotSimple
          , ruleOutMaxIntersections
          , ruleOutNormalizerOfIntersectionOrder
          , embeddingContradiction
          , transitiveActionTheorem
          , enhancedSubgroupIndex
          , multipleCountingContradiction
          ]
  
  env <- createProofEnvironment initialFacts theorems goalFact
  
  facts <- evalProofM getFacts env
  putStrLn "Initial facts:"
  mapM_ (putStrLn . ("  " ++) . formatFact) facts
  putStrLn ""
  
  putStrLn "Goal: Prove that"
  putStrLn $ "  " ++ formatFact goalFact ++ " (by assuming G is simple)"
  putStrLn ""
  
  putStrLn "Available theorems:"
  mapM_ (putStrLn . ("  - " ++) . theoremName) theorems  
  mapM_ (putStrLn . ("  - " ++) . hyperTheoremName) hyperTheorems
  
  putStrLn "Beginning automated proof search. I will attempt to derive a contradiction from the assumption that G is simple."
  (success, finalEnv) <- runProofM (enhancedAutoSolve hyperTheorems 400) env
  
  if success
    then do
      putStrLn "\nPROOF COMPLETED: a contradiction was derived from the assumption that G is simple."
      putStrLn "Conclusion: G is not simple."
      putStrLn "\nTextbook-style summary:"
      evalProofM (summarizeProof groupOrder) finalEnv
    else do
      putStrLn "\nPROOF INCONCLUSIVE: the automated search did not derive a contradiction from the assumption that G is simple."
      putStrLn "Note: this typically means Sylow's theorems do not force unique Sylow subgroups in every branch and further case analysis is required."
      
      if NT.sylowKillable groupOrder
        then do
          putStrLn "\nNote: The Sylow analysis suggests this group order is 'killable',"
          putStrLn "meaning most (or all) groups of this order are likely not simple,"
          putStrLn "but a complete proof would require more advanced techniques."
        else do
          putStrLn "\nThe Sylow analysis doesn't immediately rule out simplicity."
          putStrLn "Some groups of this order might indeed be simple."
  
  putStrLn ""
  putStrLn "=== Analysis complete ==="

-- Enhanced auto-solve using State monad
enhancedAutoSolve :: [HyperTheorem] -> Int -> ProofM Bool
enhancedAutoSolve hyperTheorems maxIterations = go 0
  where
    go iteration = do
      goalAchieved <- isGoalAchieved
      if goalAchieved
        then do
          liftIO $ putStrLn "Success: goal achieved."
          return True
        else if iteration >= maxIterations
        then do
          liftIO $ putStrLn "Max iterations reached; stopping the search to avoid excessive branching."
          return False
        else do
          facts <- getFacts
          let totalFacts = length facts
              branchFacts = length $ filter (not . Set.null . factDisAncestors) facts
              branchInfo = if branchFacts > 0 
                          then " [" ++ show branchFacts ++ "/" ++ show totalFacts ++ " facts in branches]"
                          else ""
          liftIO $ putStrLn $ "\n--- Iteration " ++ show iteration ++ branchInfo ++ " ---"
          
          -- Try to apply regular theorems first
          appliedRegular <- applyAvailableTheorems
          
          -- Then try to apply hyper-theorems  
          appliedHyper <- applyHyperTheorems hyperTheorems
          
          -- Check if we just achieved the goal
          goalNow <- isGoalAchieved
          if goalNow
            then do
              liftIO $ putStrLn "Success: goal achieved."
              return True
            else do
              if not (appliedRegular || appliedHyper)
              then do
                liftIO $ putStrLn "No further applicable theorems found."
                return False
              else
                go (iteration + 1)

-- Render a concise proof outline suitable for a textbook (now monadic)
summarizeProof :: Int -> ProofM ()
summarizeProof n = do
  facts <- getFacts
  let g = "G"
      factors = NT.primeFactorization n
      primes = map fst factors
      sylowCounts p = NT.numSylow p n
      sylowLine p = "n_" ++ show p ++ " ∈ {" ++ intercalate ", " (map show (sylowCounts p)) ++ "}"
  
  liftIO $ do
    putStrLn $ "Assume for contradiction that G is simple with |G| = " ++ show n ++ "."
    putStrLn $ "By Sylow's theorems, for each p | |G| we have: " ++ intercalate "; " (map sylowLine primes) ++ "."
    
    -- Unique Sylow implies normal
    let hasUnique p = 1 `elem` sylowCounts p
        uniquePs = filter hasUnique primes
    mapM_ (\p -> putStrLn $ "If n_" ++ show p ++ " = 1 then the Sylow-" ++ show p ++ " subgroup is normal in G, contradicting simplicity.") uniquePs
    
    -- Counting contradictions if present
    let bounds = [ (p, read m :: Int)
                 | f <- facts
                 , factName f == "order_pk_lower_bound"
                 , Just (g', p, m) <- [case factArgs f of [g', p, m] -> Just (g', p, m); _ -> Nothing]
                 , g' == g
                 ]
        maxPerP = M.toList $ M.fromListWith max bounds
        pairs = [ (p1, m1, p2, m2) | (p1, m1) <- maxPerP, (p2, m2) <- maxPerP, p1 < p2 ]
        countingHits = [ (p1, m1, p2, m2) | (p1,m1,p2,m2) <- pairs, m1 + m2 + 1 > n ]
    
    case countingHits of
      ((p1,m1,p2,m2):_) -> putStrLn $ "Moreover, there are at least " ++ show m1 ++ " elements of order divisible by " ++ p1 ++ " and at least " ++ show m2 ++ " elements of order divisible by " ++ p2 ++ "; together with the identity this exceeds |G| = " ++ show n ++ "."
      _ -> return ()
    
    -- Intersections/normalizers mentioned if present
    let hasMaxI = any (\f -> factName f == "max_sylow_intersection") facts
    when hasMaxI $ putStrLn "A short case analysis on intersections of distinct Sylow subgroups also leads to contradictions in all possibilities."
    putStrLn "Therefore, our assumption was false and G is not simple."

-- Apply available regular theorem matches (now monadic)
applyAvailableTheorems :: ProofM Bool
applyAvailableTheorems = do
  theorems <- getTheorems
  facts <- getFacts
  let allMatches = [(thm, match) | thm <- theorems, match <- matchFactsToTheorem (theoremInputFacts thm) facts Nothing]
  tryApplyMatches allMatches False
  where
    tryApplyMatches [] appliedAny = return appliedAny
    tryApplyMatches ((thm, match):rest) appliedAny = do
      result <- applyTheorem thm match
      case result of
        Nothing -> tryApplyMatches rest appliedAny
        Just newFacts -> do
          beforeCount <- length <$> getFacts
          addNewFacts newFacts
          afterCount <- length <$> getFacts
          let changed = afterCount > beforeCount
          when changed $ liftIO $ do
            putStrLn $ "Applied theorem: " ++ theoremName thm
            mapM_ (putStrLn . ("    -> " ++) . formatFact) newFacts
          tryApplyMatches rest (appliedAny || changed)

-- Propagate metadata helper (unchanged)
propagateMetadata :: Set.Set DisjunctionAncestor -> [String] -> String -> Conclusion -> Conclusion
propagateMetadata ancestors deps thName (CF fact) = 
  CF $ fact { factDisAncestors = ancestors
           , factDependencies = deps
           , factConcludingTheorem = Just thName
           }
propagateMetadata ancestors deps thName (CD disj) = 
  CD $ disj { disjunctionDisAncestors = ancestors
           , disjunctionDependencies = deps
           , disjunctionConcludingTheorem = Just thName
           }

-- Apply hyper-theorems (now monadic with cleaner state management)
applyHyperTheorems :: [HyperTheorem] -> ProofM Bool
applyHyperTheorems hyperTheorems = do
  facts <- getFacts
  let allMatches = [(hthm, match) | hthm <- hyperTheorems, match <- matchFactsToTheorem (hyperTheoremInputFacts hthm) facts Nothing]
  tryApplyHyperMatches allMatches False
  where
    tryApplyHyperMatches [] appliedAny = return appliedAny
    tryApplyHyperMatches ((hthm, match):rest) appliedAny = do
      -- Branch compatibility check (same logic)
      let disAncLists = map factDisAncestors match
          pairs = concatMap Set.toList disAncLists :: [DisjunctionAncestor]
          labelToIdxs :: M.Map String (Set.Set Int)
          labelToIdxs = M.fromListWith Set.union [(lbl, Set.singleton idx) | (lbl, idx) <- pairs]
          compatible = all (\s -> Set.size s <= 1) (M.elems labelToIdxs)
      
      if not compatible
        then tryApplyHyperMatches rest appliedAny
        else do
          let conclusions = hyperTheoremRule hthm match
          if null conclusions
            then tryApplyHyperMatches rest appliedAny
            else do
              -- Propagate metadata
              let inputDisAncestors = Set.unions (map factDisAncestors match)
                  dependencyLabels = [fromMaybe "" (factLabel fact) | fact <- match]
                  conclusionsWithMetadata = map (propagateMetadata inputDisAncestors dependencyLabels (hyperTheoremName hthm)) conclusions
                  hname = hyperTheoremName hthm
              
              -- Add conclusions and check for changes
              beforeFacts <- length <$> getFacts  
              beforeDisjs <- length <$> getDisjunctions
              addConclusions conclusionsWithMetadata
              afterFacts <- length <$> getFacts
              afterDisjs <- length <$> getDisjunctions
              let changed = (afterFacts > beforeFacts) || (afterDisjs > beforeDisjs)
              
              -- Print summary (same logic but cleaner structure)
              when changed $ do
                disjs <- getDisjunctions
                let findLabelForDisj dj =
                      let sig f = (factName f, factArgs f)
                          target = Set.fromList (map sig (disjunctionFacts dj))
                          matches = [ fromMaybe (hname ++ "-cases") (disjunctionLabel d)
                                    | d <- disjs
                                    , Set.fromList (map sig (disjunctionFacts d)) == target
                                    ]
                      in case matches of
                           (l:_) -> l
                           []    -> hname ++ "-cases"
                
                liftIO $ printHyperTheoremSummary hname conclusions changed findLabelForDisj
              
              tryApplyHyperMatches rest (appliedAny || changed)

-- Print hyper-theorem summary (extracted for clarity)
printHyperTheoremSummary :: String -> [Conclusion] -> Bool -> (Disjunction -> String) -> IO ()
printHyperTheoremSummary hname conclusions changed findLabelForDisj = 
  case hname of
    "sylow" -> do
      let numPairs = [ (p', n')
                     | CD d <- conclusions
                     , f <- disjunctionFacts d
                     , factName f == "num_sylow"
                     , let args = factArgs f
                     , Just (p', n') <- [case args of [p1, _g, n1] -> Just (p1, n1); _ -> Nothing]
                     ]
          primes = nub [p | (p, _) <- numPairs]
          parts = [ p ++ ": n_" ++ p ++ " ∈ {" ++ intercalate ", " (sort (Set.toList (Set.fromList [n | (p', n) <- numPairs, p' == p]))) ++ "}"
                  | p <- primes
                  ]
          summaryText = if null parts
                          then "By Sylow's theorem no immediate numerical constraints were derived."
                          else "By Sylow's theorem, " ++ intercalate "; " parts ++ ". We will examine the possible combinations of these counts."
      putStrLn summaryText
    
    "single_sylow_normal" ->
      putStrLn "If a Sylow p-subgroup is unique then it is normal; this contradicts simplicity when G is assumed simple."
    
    "normal_subgroup_to_not_simple" ->
      putStrLn "A nontrivial normal subgroup (1 < |H| < |G|) contradicts simplicity, so G is not simple."
    
    "p_group_not_simple" ->
      putStrLn "If |G| is a prime power p^k with k>=2 then G is a nontrivial p-group and hence not simple."
    
    "counting_contradiction" ->
      putStrLn "Counting argument: elements of different prime orders cannot overlap, leading to a size contradiction."
    
    _ -> do
      -- Default: bundle the conclusions into readable sentences  
      let facts = [ f | CF f <- conclusions ]
          disjs = [ d | CD d <- conclusions ]
          sentence1 = if null facts then "" else "Hence: " ++ intercalate "; " (map formatFact facts) ++ "."
          sentence2 = if null disjs then "" else "Also consider the following case distinctions: " ++ intercalate "; " (map (\dj -> let ds = disjunctionFacts dj in "{" ++ intercalate ", " (map formatFact ds) ++ "}") disjs) ++ "."
      when (not (null sentence1) && changed) $ putStrLn sentence1
      when (not (null disjs) && changed) $ do
        putStrLn sentence2
        mapM_ (\dj -> putStrLn $ formatDisjunctionDetailed (findLabelForDisj dj) dj) disjs

-- Helper functions (unchanged from original)
getGroupOrderFromUser :: IO Int
getGroupOrderFromUser = do
  putStrLn "Enter a group order to analyze (positive integer, or press Enter for default 60):"
  userInput <- getLine
  case userInput of
    "" -> return 60
    input -> case readMaybe input of
      Just n | n > 0 -> return n
      _ -> do
        putStrLn "Please enter a positive integer. Try again:"
        getGroupOrderFromUser

analyzeGroupOrder :: Int -> IO ()
analyzeGroupOrder n = do
  putStrLn $ "Mathematical analysis of groups of order " ++ show n ++ ":"
  let primes = NT.primeFactors n
      factorization = NT.primeFactorization n
  putStrLn $ "Prime factorization: " ++ show n ++ " = " ++ showFactorization factorization
  putStrLn "\nSylow subgroup analysis:"
  mapM_ (analyzeSylowForPrime n) primes
  let killable = NT.sylowKillable n
  putStrLn $ "\nIs this group order Sylow-killable? " ++ show killable
  if killable
    then putStrLn "  → This suggests groups of this order might not be simple!"
    else putStrLn "  → Groups of this order could potentially be simple."
  putStrLn ""

showFactorization :: [(Int, Int)] -> String
showFactorization [] = "1"
showFactorization [(p, 1)] = show p
showFactorization [(p, e)] = show p ++ "^" ++ show e
showFactorization ((p, 1):rest) = show p ++ " × " ++ showFactorization rest
showFactorization ((p, e):rest) = show p ++ "^" ++ show e ++ " × " ++ showFactorization rest

analyzeSylowForPrime :: Int -> Int -> IO ()
analyzeSylowForPrime n p = do
  let maxPower = NT.maxPDivisor n p
      sylowOrder = p ^ maxPower
      possibleCounts = NT.numSylow p n
      isKillable = NT.pKillable p n
  putStrLn $ "  " ++ show p ++ "-Sylow subgroups:"
  putStrLn $ "    Order: " ++ show sylowOrder ++ " (= " ++ show p ++ "^" ++ show maxPower ++ ")"
  putStrLn $ "    Possible counts: " ++ show possibleCounts
  putStrLn $ "    " ++ show p ++ "-killable: " ++ show isKillable