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
import Control.Monad (when, unless)
import Control.Monad.State.Strict
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Maybe (fromMaybe)

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
    } deriving (Show)

-- | The ProofM monad wraps State ProofEnvironment with IO for printing
newtype ProofM a = ProofM { unProofM :: StateT ProofEnvironment IO a }
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
        }
  -- Add initial facts using the ProofM monad
  env1 <- execProofM (addNewFacts facts) initialEnv
  let symbolSet = Set.fromList $ concatMap factArgs (peFacts env1)
  return $ env1 { peSymbolSet = symbolSet }

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

-- | Update goal achievement status - now monadic
updateGoalAchieved :: Fact -> ProofM ()
updateGoalAchieved _goalFact = do
  goalCombos <- gets peGoalDisCombos
  disjs <- gets peDisjunctions
  
  -- Extract all disjunction labels from goal combinations
  let fullDisSet = Set.fromList [d | combo <- goalCombos, (d, _) <- Set.toList combo]
      
      -- Get sizes for each disjunction
      disjunctionSizes = [(disjLabel, length (disjunctionFacts dj))
                         | dj <- disjs
                         , let disjLabel = fromMaybe "" (disjunctionLabel dj)
                         , not (null disjLabel)
                         , Set.member disjLabel fullDisSet
                         ]
      
      -- Generate all possible case combinations
      allPossibleCombos = generateAllPossibleCombinations disjunctionSizes
      
      -- Check complete coverage
      allCovered = all (isComboCoveredByGoal goalCombos) allPossibleCombos
  
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
isComboCoveredByGoal :: [Set DisjunctionAncestor] -> Set DisjunctionAncestor -> Bool
isComboCoveredByGoal goalCombos combination =
  any (\combo -> Set.isSubsetOf combo combination) goalCombos

-- | Update useful facts - now monadic
updateUseful :: FactLabel -> ProofM ()
updateUseful factLabel = do
  factLabels <- gets peFactLabels
  case Map.lookup factLabel factLabels of
    Nothing -> return ()
    Just fact -> do
      unless (factUseful fact) $ do
        let updatedFact = fact { factUseful = True }
        modify $ \env -> env { peFactLabels = Map.insert factLabel updatedFact (peFactLabels env) }
        mapM_ updateUseful (factDependencies fact)

-- | Add new facts - now monadic with automatic state management
addNewFacts :: [Fact] -> ProofM ()
addNewFacts [] = return ()
addNewFacts (fact:rest) = do
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
      
      -- Check for goal match
      goal <- getGoal
      when (factName fact == factName goal && factArgs fact == factArgs goal) $ do
        modify $ \env -> env { peGoalDisCombos = factDisAncestors fact : peGoalDisCombos env }
        updateGoalAchieved fact
        updateUseful label
      
      addNewFacts rest

-- | Add new disjunctions - now monadic
addNewDisjunctions :: [Disjunction] -> ProofM ()  
addNewDisjunctions [] = return ()
addNewDisjunctions (disj:rest) = do
  disjs <- getDisjunctions
  let isDuplicate = disjunctionExists disj disjs
  
  if isDuplicate
    then addNewDisjunctions rest
    else do
      label <- newLabel "D"
      let disjWithLabel = disj { disjunctionLabel = Just label }
      
      addDisjunction disjWithLabel
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
  let facts = [f | CF f <- concs]
      disjs = [d | CD d <- concs]
  addNewFacts facts
  addNewDisjunctions disjs
  pruneDisjunctions

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
  facts <- getFacts
  disjs <- getDisjunctions
  
  -- Find false facts that eliminate disjunction alternatives (same logic)
  let isFalse f = factName f == "false"
      falseFacts = filter isFalse facts
      
      -- Only eliminate if contradiction depends on exactly one alternative
      directElims = [ pair
                    | f <- falseFacts
                    , let anc = factDisAncestors f
                    , Set.size anc == 1
                    , let [pair] = Set.toList anc
                    ]
      
      elimMap = foldr (\(d,i) m -> Map.insertWith Set.union d (Set.singleton i) m) Map.empty directElims
      
      -- Find promotable facts (when only one alternative remains)
      djInfo = [ ( label
                 , length (disjunctionFacts dj)
                 , zip [0..] (disjunctionFacts dj)
                 )
               | dj <- disjs
               , let label = fromMaybe "" (disjunctionLabel dj)
               , not (null label)
               ]
      
      promotable = [ (label, j, f)
                   | (label, k, pairs) <- djInfo
                   , Just elim <- [Map.lookup label elimMap]
                   , let remaining = [ idx | (idx, _) <- pairs, not (Set.member idx elim) ]
                   , length remaining == 1
                   , let j = head remaining
                   , (_, f) <- pairs
                   , let hasJ = Set.member (label, j) (factDisAncestors f)
                   , hasJ
                   ]
      
      promotedFacts = [ f { factDisAncestors = Set.delete (label, j) (factDisAncestors f) }
                      | (label, j, f) <- promotable
                      ]
  
  unless (null promotedFacts) $ addNewFacts promotedFacts

-- | Print derivation - now monadic
printDerivation :: FactLabel -> ProofM ()
printDerivation factLabel = do
  factLabels <- gets peFactLabels
  case Map.lookup factLabel factLabels of
    Nothing -> liftIO $ putStrLn $ "Fact " ++ factLabel ++ " not found."
    Just fact -> liftIO $ putStrLn $ "Fact: " ++ show fact