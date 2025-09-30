{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | StateEnvironment.hs
--
-- State monad-based proof environment implementation 
-- This refactors the manual state threading to use proper monadic composition

module StateEnvironment (
    ProofEnvironment(..),
    ProofM,
    runProofM,
    evalProofM,
    execProofM,
    createProofEnvironment,
    generateNewSymbol,
    newLabel,
    updateGoalAchieved,
    addNewFacts,
    addNewDisjunctions,
    addConclusions,
    applyTheorem,
    updateUseful,
    pruneDisjunctions,
    printDerivation,
    -- State accessors
    getFacts,
    getTheorems,
    getDisjunctions,
    getGoal,
    isGoalAchieved,
    -- State modifiers
    addFact,
    addDisjunction,
    setGoalAchieved
) where

import Core
-- when/unless are available from Prelude in recent GHCs; avoid redundant import
import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)
import System.IO (IOMode(AppendMode), hPutStrLn, withFile)
import Data.List (intercalate, sort)
import Data.Bits (xor)

-- | Type aliases for clarity
type FactMap = Map FactLabel Fact
type TheoremMap = Map String Theorem

-- | Proof environment state - same data structure but now managed by State monad
data ProofEnvironment = ProofEnvironment
    { peFacts :: [Fact]
    , peFactMap :: FactMap
    , peTheorems :: [Theorem]
    , peTheoremMap :: TheoremMap
    , peDisjunctions :: [Disjunction]
  , peDisjunctionMap :: Map String Disjunction
    , peGoal :: Fact
    , peGoalAchieved :: Bool
    , peGoalDisCombos :: [Set DisjunctionAncestor]
    , peFactLabels :: Map FactLabel Fact
    , peCurFactNum :: Int
    , peSymbolSet :: Set String
    , peCurLetter :: Char
    , peCurSuffix :: Int
    , peCaseDepth :: Int
    , peNumCases :: Int
    , peSolvedCases :: Int
    , peCaseDisjunction :: Maybe Disjunction
    , peCaseFact :: Maybe Fact
  , peDiagnosticJsonPath :: Maybe FilePath
    } deriving (Show)

-- | The ProofM monad wraps State ProofEnvironment with IO for printing
newtype ProofM a = ProofM (StateT ProofEnvironment IO a)
  deriving newtype (Functor, Applicative, Monad, MonadState ProofEnvironment, MonadIO)

-- | Run the ProofM computation, returning both result and final state
runProofM :: ProofM a -> ProofEnvironment -> IO (a, ProofEnvironment)
runProofM (ProofM action) = runStateT action

-- | Run ProofM and return only the result, discarding final state
evalProofM :: ProofM a -> ProofEnvironment -> IO a
evalProofM (ProofM action) = evalStateT action

-- | Run ProofM and return only the final state, discarding result
execProofM :: ProofM a -> ProofEnvironment -> IO ProofEnvironment
execProofM (ProofM action) = execStateT action

-- | Create initial proof environment (returns monadic action)
createProofEnvironment :: [Fact] -> [Theorem] -> Fact -> IO ProofEnvironment
createProofEnvironment facts theorems goal = do
  let initialEnv = ProofEnvironment
        { peFacts = []
        , peFactMap = Map.empty
        , peTheorems = theorems
        , peTheoremMap = Map.fromList [(theoremName thm, thm) | thm <- theorems]
        , peDisjunctions = []
        , peGoal = goal
        , peGoalAchieved = False
        , peGoalDisCombos = []
        , peFactLabels = Map.empty
        , peCurFactNum = 0
        , peSymbolSet = Set.empty
        , peCurLetter = 'A'
        , peCurSuffix = 0
        , peCaseDepth = 0
        , peNumCases = 0
        , peSolvedCases = 0
        , peCaseDisjunction = Nothing
        , peCaseFact = Nothing
  , peDiagnosticJsonPath = Nothing
    , peDisjunctionMap = Map.empty
        }
  -- Add initial facts using the ProofM monad
  env1 <- execProofM (addNewFacts facts) initialEnv
  let symbolSet = Set.fromList $ concatMap factArgs (peFacts env1)
  -- Build the disjunction map from any disjunctions registered during
  -- initialization so newDisjunctionLabel can consult it consistently.
  let disjPairs = [ (lbl, dj) | dj <- peDisjunctions env1, let lbl = case disjunctionLabel dj of Just l -> l; Nothing -> "" , lbl /= "" ]
      disjMap = Map.fromList disjPairs
  return $ env1 { peSymbolSet = symbolSet, peDisjunctionMap = disjMap }

-- ============================================================================
-- State Accessors (clean monadic interface)
-- ============================================================================

getFacts :: ProofM [Fact]
getFacts = gets peFacts

getTheorems :: ProofM [Theorem]
getTheorems = gets peTheorems

getDisjunctions :: ProofM [Disjunction]  
getDisjunctions = gets peDisjunctions

getGoal :: ProofM Fact
getGoal = gets peGoal

isGoalAchieved :: ProofM Bool
isGoalAchieved = gets peGoalAchieved

-- ============================================================================
-- State Modifiers (clean monadic interface)
-- ============================================================================

addFact :: Fact -> ProofM ()
addFact fact = modify $ \env -> env { peFacts = peFacts env ++ [fact] }

addDisjunction :: Disjunction -> ProofM ()
addDisjunction disj = modify $ \env -> env { peDisjunctions = peDisjunctions env ++ [disj] }

setGoalAchieved :: Bool -> ProofM ()
setGoalAchieved achieved = modify $ \env -> env { peGoalAchieved = achieved }

-- ============================================================================
-- Core Functions (now monadic)
-- ============================================================================

-- | Generate new symbol - now returns in ProofM
generateNewSymbol :: ProofM String
generateNewSymbol = do
  env <- get
  let currentLetter = peCurLetter env
      currentSuffix = peCurSuffix env
      suffix = if currentSuffix == 0 then "" else show currentSuffix
      newSymbol = [currentLetter] ++ suffix
  
  if Set.member newSymbol (peSymbolSet env)
    then do
      -- Advance to next letter/suffix and try again
      if currentLetter == 'Z'
        then modify $ \e -> e { peCurLetter = 'A', peCurSuffix = currentSuffix + 1 }
        else modify $ \e -> e { peCurLetter = succ currentLetter }
      generateNewSymbol
    else do
      -- Use this symbol and advance state
      if currentLetter == 'Z'
        then modify $ \e -> e { peCurLetter = 'A', peCurSuffix = currentSuffix + 1, peSymbolSet = Set.insert newSymbol (peSymbolSet e) }
        else modify $ \e -> e { peCurLetter = succ currentLetter, peSymbolSet = Set.insert newSymbol (peSymbolSet e) }
      return newSymbol

-- | Generate new label - now returns in ProofM  
newLabel :: String -> ProofM FactLabel
newLabel prefix = do
  env <- get
  let label = prefix ++ show (peCurFactNum env)
  modify $ \e -> e { peCurFactNum = peCurFactNum e + 1 }
  return label

-- | Produce a deterministic disjunction label from a canonical signature
newDisjunctionLabel :: Disjunction -> String -> ProofM FactLabel
newDisjunctionLabel disj prefix = do
  -- Build canonical signature for this disjunction
  let canon = canonicalDisjunctionSignature disj
      num = (abs $ hashString canon) `mod` 1000000
      label0 = prefix ++ show num

  -- If a disjunction with the same numeric label already exists, reuse
  -- it when the canonical signatures match. We keep a dedicated map of
  -- disjunction-label -> Disjunction for this purpose (peDisjunctionMap).
  existing <- gets (Map.lookup label0 . peDisjunctionMap)
  -- define probe inside the do-block so it can capture `num` and `disj`
  let probe :: Int -> ProofM FactLabel
      probe n = do
        let lbl = prefix ++ show ((num + n) `mod` 1000000)
        existing' <- gets (Map.lookup lbl . peDisjunctionMap)
        case existing' of
          Nothing -> return lbl
          Just ex2 -> if canonicalDisjunctionSignature ex2 == canonicalDisjunctionSignature disj
                        then return lbl
                        else probe (n + 1)
  case existing of
    Just ex -> if canonicalDisjunctionSignature ex == canon
                 then return label0
                 else probe 1
    Nothing -> return label0

-- Very small non-cryptographic hash for determinism and portability
hashString :: String -> Int
hashString = abs . foldl (\h c -> h * 16777619 `xor` fromEnum c) 2166136261

-- | Build canonical disjunction signature (pure helper)
canonicalDisjunctionSignature :: Disjunction -> String
canonicalDisjunctionSignature d =
  let sigs = map (\f -> factName f ++ ":" ++ intercalate "," (factArgs f)) (disjunctionFacts d)
      sortedSigs = sort sigs
      thmPart = case disjunctionConcludingTheorem d of
                  Just t -> ["thm:" ++ t]
                  Nothing -> []
      ancSet = disjunctionDisAncestors d
      ancLabels = sort $ map fst (Set.toList ancSet)
      ancPart = if null ancLabels then [] else ["anc:" ++ intercalate "," ancLabels]
  in intercalate "|" (sortedSigs ++ thmPart ++ ancPart)

-- | Update goal achievement status - now monadic
updateGoalAchieved :: Fact -> ProofM ()
updateGoalAchieved _goalFact = do
  goalCombos <- gets peGoalDisCombos
  disjs <- gets peDisjunctions

  -- Extract all disjunction labels from goal combinations
  let fullDisSet = Set.fromList [d | combo <- goalCombos, (d, _) <- Set.toList combo]

      -- Get sizes for each disjunction
      disjunctionSizes = [ (disjLabel, length (disjunctionFacts dj))
                        | dj <- disjs
                        , let disjLabel = fromMaybe "" (disjunctionLabel dj)
                        , not (null disjLabel)
                        , Set.member disjLabel fullDisSet
                        ]

      -- Generate all possible case combinations
      allPossibleCombos = generateAllPossibleCombinations disjunctionSizes

      -- Check complete coverage
      comboCoverings = map (\full -> (full, filter (\g -> Set.isSubsetOf g full) goalCombos)) allPossibleCombos
      allCovered = all (not . null . snd) comboCoverings

  factLabels <- gets peFactLabels
  let -- helper: find facts that have exactly the given disjunction-ancestor set
      findFactsByAnc anc = [ (lbl, f) | (lbl, f) <- Map.toList factLabels, factDisAncestors f == anc ]

  -- Debugging instrumentation: print the goal coverage details so we can
  -- understand why the environment believes every case combination is
  -- covered (which would set the global goal flag). This helps diagnose
  -- cases like order 60 where a full contradiction should not hold.
  liftIO $ do
    putStrLn $ "DEBUG updateGoalAchieved: goalCombos = " ++ show goalCombos
    putStrLn $ "DEBUG disjunctionSizes = " ++ show disjunctionSizes
    putStrLn $ "DEBUG allPossibleCombos count = " ++ show (length allPossibleCombos)
    -- Print a small sample of the per-combination coverings to diagnose
    -- why every full assignment appears to be covered. For large numbers of
    -- combinations we only show the first 20 entries.
    let sample = take 20 comboCoverings
    mapM_ (\(f, covers) -> do
             putStrLn $ "  fullCombo: " ++ show (Set.toList f) ++ "  coveredBy: " ++ show (map Set.toList covers)
             -- For each covering observed combo, list fact labels/signatures that produced that ancestor set
             mapM_ (\g -> do
                       let producers = findFactsByAnc g
                       unless (null producers) $ putStrLn $ "    producers for " ++ show (Set.toList g) ++ " -> " ++ show (map (\(l,ff) -> (l, factName ff, factArgs ff)) producers)
                   ) covers
          ) sample
    putStrLn $ "DEBUG allCovered = " ++ show allCovered
    -- If not all covered, print a compact summary of uncovered combos so
    -- we can inspect which full assignments are missing producers.
    unless allCovered $ do
      let uncovered = filter (null . snd) comboCoverings
      putStrLn $ "DEBUG uncovered count = " ++ show (length uncovered)
      let sampleUncov = take 10 uncovered
      mapM_ (\(full, _) -> putStrLn $ "  uncovered fullCombo: " ++ show (Set.toList full)) sampleUncov

  -- Optionally write a JSON-lines diagnostics file matching the Python
  -- reporter when a path is provided in the environment. We keep the
  -- format minimal and structural so the existing compare tooling can
  -- consume it.
  mpath <- gets peDiagnosticJsonPath
  case mpath of
    Nothing -> return ()
    Just path -> do
      -- Pure helpers to render JSON-like structures
      let serializeAnc :: (String, Int) -> String
          serializeAnc (lbl, idx) = "[" ++ show lbl ++ "," ++ show idx ++ "]"

          serializeAncSet :: Set DisjunctionAncestor -> String
          serializeAncSet s = "[" ++ intercalate "," (map serializeAnc (Set.toList s)) ++ "]"

          -- Sort combos deterministically by their JSON-like string
          serializeGoalDisCombos :: [Set DisjunctionAncestor] -> String
          serializeGoalDisCombos gcs =
            let lists = map (map (\(l,i) -> (l,i)) . Set.toList) gcs
                asJsonLike = map (\lst -> "[" ++ intercalate "," (map (\(l,i) -> "[" ++ show l ++ "," ++ show i ++ "]") lst) ++ "]") lists
                sorted = sort asJsonLike
            in "[" ++ intercalate "," sorted ++ "]"

          serializeDisSizes :: [(String, Int)] -> String
          serializeDisSizes ds = "[" ++ intercalate "," (map (\(l,n) -> "[" ++ show l ++ "," ++ show n ++ "]") ds) ++ "]"

          serializeArgs :: [String] -> String
          serializeArgs args = "[" ++ intercalate "," (map show args) ++ "]"

          producersFor :: Set DisjunctionAncestor -> String
          producersFor rc = let prods = findFactsByAnc rc
                            in "[" ++ intercalate "," (map (\(_,f) -> "[" ++ show (factName f) ++ "," ++ serializeArgs (factArgs f) ++ "]") prods) ++ "]"

          serializeFactSig f = "[" ++ show (factName f) ++ "," ++ serializeArgs (factArgs f) ++ "]"
          -- include canonical signature as a third element for each disjunction
          disjunctionSignaturesStr = "[" ++ intercalate "," (map (\f -> let lbl = fromMaybe "" (disjunctionLabel f)
                                                                                   in "[" ++ show lbl ++ "," ++ "[" ++ intercalate "," (map serializeFactSig (disjunctionFacts f)) ++ "]" ++ "," ++ show (canonicalDisjunctionSignature f) ++ "]") disjs) ++ "]"

          headerStr = "{\"type\": \"header\", \"data\": {\"goal_dis_combos\": " ++ serializeGoalDisCombos goalCombos ++ ", \"disjunctionSizes\": " ++ serializeDisSizes disjunctionSizes ++ ", \"disjunctionSignatures\": " ++ disjunctionSignaturesStr ++ ", \"allPossibleCombos\": " ++ show (length allPossibleCombos) ++ "}}"

      liftIO $ withFile path AppendMode (\h -> do
        hPutStrLn h headerStr
        -- write each combo
        mapM_ (\i -> do
               let (full, covers) = comboCoverings !! i
                   full_json = serializeAncSet full
                   covered_json = "[" ++ intercalate "," (map serializeAncSet covers) ++ "]"
                   producers_json = "[" ++ intercalate "," (map producersFor covers) ++ "]"
                   producers_for_full = producersFor full
                   comboLine = "{\"type\": \"combo\", \"index\": " ++ show i ++ ", \"data\": {\"full_combo\": " ++ full_json ++ ", \"covered_by\": " ++ covered_json ++ ", \"producers\": " ++ producers_json ++ ", \"producers_for_full\": " ++ producers_for_full ++ "}}"
               hPutStrLn h comboLine
            ) [0 .. length comboCoverings - 1])
      return ()

  when (allCovered && not (null goalCombos) && not (null allPossibleCombos)) $
    setGoalAchieved True

-- | Generate all possible combinations - pure helper (unchanged)
generateAllPossibleCombinations :: [(String, Int)] -> [Set DisjunctionAncestor]
generateAllPossibleCombinations [] = [Set.empty]
generateAllPossibleCombinations ((label, size):rest) =
  let restCombos = generateAllPossibleCombinations rest
      thisCases = [(label, i) | i <- [0..size-1]]
  in [Set.insert thisCase restCombo | thisCase <- thisCases, restCombo <- restCombos]

-- | Check coverage - pure helper (unchanged)
-- NOTE: coverage check helper removed; keep the logic local in updateGoalAchieved

-- | Update useful facts - now monadic
updateUseful :: FactLabel -> ProofM ()
updateUseful flbl = do
  factLabels <- gets peFactLabels
  case Map.lookup flbl factLabels of
    Nothing -> return ()
    Just fact -> do
      unless (factUseful fact) $ do
        let updatedFact = fact { factUseful = True }
        modify $ \env -> env { peFactLabels = Map.insert flbl updatedFact (peFactLabels env) }
        mapM_ updateUseful (factDependencies fact)

-- | Add new facts - now monadic with automatic state management
addNewFacts :: [Fact] -> ProofM ()
addNewFacts [] = return ()
addNewFacts (fact:rest) = do
  -- If we've already found the goal (false/contradiction), skip further work
  achieved <- gets peGoalAchieved
  if achieved then return () else do
    facts <- getFacts
    let duplicateExists = any (\f -> factName f == factName fact
                                   && factArgs f == factArgs fact
                                   && factDisAncestors f == factDisAncestors fact) facts

    if duplicateExists
      then addNewFacts rest
      else do
      label <- newLabel "F"
      let factWithLabel = fact { factLabel = Just label }
      
      -- Update state monadically
      modify $ \env -> env 
        { peFacts = peFacts env ++ [factWithLabel]
        , peFactLabels = Map.insert label factWithLabel (peFactLabels env)
        }

      -- Instrumentation: print a concise trace line for the added fact so
      -- we can compare Haskell's derivation trace with Python's output.
      liftIO $ do
        putStrLn $ label ++ "  :  " ++ factName factWithLabel ++ "   " ++ show (factArgs factWithLabel)
        case factConcludingTheorem factWithLabel of
          Just th -> putStrLn $ "    by thm  " ++ th ++ ""
          Nothing -> return ()
        let anc = Set.toList (factDisAncestors factWithLabel)
        unless (null anc) $ putStrLn $ "    Disjunctions in history: " ++ show anc
      
      -- Check for goal match (do not prematurely set global goal on a
      -- single-branch 'false' — rely on updateGoalAchieved to decide when
      -- the goal is covered across all case combinations)
      goal <- getGoal
      when (factName fact == factName goal && factArgs fact == factArgs goal) $ do
        -- Debug: print the fact and its disjunction ancestry when it is
        -- recorded as a goal-disjunction combo. This helps trace which
        -- observed contradictions contribute singleton or composite
        -- ancestor sets that later cause full coverage.
        -- Also print a signature-mapped version of the ancestor set so we
        -- can compare across Haskell/Python runs where disjunction labels
        -- differ. For each (Dlabel, idx) we attempt to lookup the
        -- corresponding disjunction alternative's (name,args).
        disjs <- gets peDisjunctions
        let lookupSig (dlabel, idx) = case filter (\dj -> disjunctionLabel dj == Just dlabel) disjs of
              (dj:_) -> let alts = disjunctionFacts dj in if idx < length alts then Just (factName (alts !! idx), factArgs (alts !! idx)) else Nothing
              [] -> Nothing
            sigs = [ (ti, lookupSig ti) | ti <- Set.toList (factDisAncestors fact) ]
        liftIO $ do
          putStrLn $ "DEBUG addNewFacts: recording goal combo from " ++ label ++ " -> " ++ show (Set.toList (factDisAncestors fact))
          putStrLn $ "DEBUG addNewFacts: signature-mapped ancestors: " ++ show sigs
        modify $ \env -> env { peGoalDisCombos = factDisAncestors fact : peGoalDisCombos env }
        updateGoalAchieved fact
        updateUseful label
      
      addNewFacts rest

-- | Add new disjunctions - now monadic
addNewDisjunctions :: [Disjunction] -> ProofM ()  
addNewDisjunctions [] = return ()
addNewDisjunctions (disj:rest) = do
  achieved <- gets peGoalAchieved
  if achieved then return () else do
    disjs <- getDisjunctions
    let isDuplicate = disjunctionExists disj disjs

    if isDuplicate
      then addNewDisjunctions rest
      else do
        label <- newDisjunctionLabel disj "D"
        let disjWithLabel = disj { disjunctionLabel = Just label }

        -- Print a summary for the disjunction and its alternatives
        liftIO $ do
          putStrLn $ label ++ " :"
          mapM_ (\(_i,f) -> putStrLn $ show f ++ "\n    OR") (zip [0 :: Int ..] (disjunctionFacts disjWithLabel))

        addDisjunction disjWithLabel
        -- register in the disjunction map for canonical lookup
        modify $ \env -> env { peDisjunctionMap = Map.insert label disjWithLabel (peDisjunctionMap env) }
        processDisjunctionFacts disjWithLabel
        addNewDisjunctions rest

-- | Check if disjunction exists - pure helper (unchanged)
disjunctionExists :: Disjunction -> [Disjunction] -> Bool
disjunctionExists disj existingDisjs = any (sameAltFacts disj) existingDisjs
  where
    sig :: Fact -> (String, [String])
    sig f = (factName f, factArgs f)
    toSet ds = Set.fromList (map sig (disjunctionFacts ds))
    sameAltFacts d1 d2 = toSet d1 == toSet d2

-- | Process disjunction facts - now monadic
processDisjunctionFacts :: Disjunction -> ProofM ()
processDisjunctionFacts disj = do
  let disjLabel = fromMaybe "" (disjunctionLabel disj)
      processedFacts = zipWith (processSubFact disjLabel (disjunctionDisAncestors disj)) [0..] (disjunctionFacts disj)
  addNewFacts processedFacts
  where
    processSubFact :: String -> Set DisjunctionAncestor -> Int -> Fact -> Fact
    processSubFact label disAncestors index fact =
      fact { factDependencies = [label]
           , factDisAncestors = Set.insert (label, index) disAncestors
           }

-- | Add conclusions - now monadic
addConclusions :: [Conclusion] -> ProofM ()
addConclusions concs = do
  -- Short-circuit: if goal already achieved, skip adding conclusions
  achieved <- gets peGoalAchieved
  if achieved then return () else do

    -- First, instantiate any placeholder symbols ("?x") appearing in the
    -- newly-produced conclusions. The Python reference replaces these with
    -- generated concrete symbols before adding facts; the Haskell port must do
    -- the same so subsequent matching behaves identically.
    instantiated <- processNewConclusions concs
    let facts = [f | CF f <- instantiated]
        disjs = [d | CD d <- instantiated]
    -- Add disjunctions first so their labels exist before any facts that
    -- reference those disjunction ancestors are processed. This mirrors the
    -- Python reference which registers a Disjunction and then adds its
    -- alternative facts (so derived facts can refer to the disjunction
    -- label when update_goal_achieved runs).
    addNewDisjunctions disjs
    addNewFacts facts
    pruneDisjunctions


-- | Replace placeholder variables (strings starting with '?') in a batch of
-- conclusions with newly-generated concrete symbols. This mirrors Python's
-- `process_new_facts` behavior where all '?'-variables in the same batch are
-- replaced consistently.
processNewConclusions :: [Conclusion] -> ProofM [Conclusion]
processNewConclusions concs = do
  -- Collect all simple facts appearing in the conclusions (flatten disjunctions)
  let collectSimple (CF f) = [f]
      collectSimple (CD d) = disjunctionFacts d
      simpleFacts = concatMap collectSimple concs

  -- Gather unique placeholder keys (strings starting with '?')
  let collectPlaceholders acc fact =
        foldr (\tok m -> if not (null tok) && head tok == '?' then Map.insert tok () m else m) acc (factArgs fact)
      placeholderMap = foldl collectPlaceholders Map.empty simpleFacts
      placeholderKeys = Map.keys placeholderMap

  -- Generate concrete symbols for each placeholder (preserve order)
  mappingsList <- mapM (\ph -> do { sym <- generateNewSymbol; return (ph, sym) }) placeholderKeys
  let mappings = Map.fromList mappingsList

  -- Replace placeholder args in a fact according to mappings
  let replaceFactArgs fact = fact { factArgs = map (\a -> if not (null a) && head a == '?' then fromMaybe a (Map.lookup a mappings) else a) (factArgs fact) }

  -- Apply replacement across all conclusions
  let instantiated = map (\c -> case c of
                                   CF f -> CF (replaceFactArgs f)
                                   CD d -> CD (d { disjunctionFacts = map replaceFactArgs (disjunctionFacts d) })
                         ) concs
  return instantiated

-- | Apply theorem - now returns ProofM (Maybe [Fact])
applyTheorem :: Theorem -> [Fact] -> ProofM (Maybe [Fact])
applyTheorem theorem facts = do
  -- Branch compatibility check (same logic)
  let disAncLists = map factDisAncestors facts
      pairs = concatMap Set.toList disAncLists :: [DisjunctionAncestor]
      labelToIdxs :: Map String (Set Int)
      labelToIdxs = Map.fromListWith Set.union [(lbl, Set.singleton idx) | (lbl, idx) <- pairs]
      compatible = all (\s -> Set.size s <= 1) (Map.elems labelToIdxs)
  
  if not compatible || length facts /= length (theoremInputFacts theorem)
    then return Nothing
    else do
      let newDisAncestors = Set.unions (map factDisAncestors facts)
          dependencyLabels = [fromMaybe "" (factLabel fact) | fact <- facts]
          newFacts = [ fact { factDisAncestors = newDisAncestors
                            , factDependencies = dependencyLabels
                            , factConcludingTheorem = Just (theoremName theorem)
                            }
                     | fact <- theoremConclusions theorem ]
      return (Just newFacts)

-- | Prune disjunctions - now monadic
pruneDisjunctions :: ProofM ()
pruneDisjunctions = do
  -- Intentionally a no-op: we avoid promoting alternatives to preserve
  -- parity with the Python implementation which does not mutate ancestry
  -- sets. Previously this function performed eliminations that led to
  -- incorrect global contradictions on some inputs.
  return ()

-- | Print derivation - now monadic
printDerivation :: FactLabel -> ProofM ()
printDerivation flbl = do
  factLabels <- gets peFactLabels
  case Map.lookup flbl factLabels of
    Nothing -> liftIO $ putStrLn $ "Fact " ++ flbl ++ " not found."
    Just fact -> liftIO $ putStrLn $ "Fact: " ++ show fact