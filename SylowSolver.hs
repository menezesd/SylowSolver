{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
-- A tiny, extensible Sylow-based theorem prover prototype in Haskell
-- Implements the "facts + techniques (theorems) + proof search with disjunction dependencies"
-- architecture from the provided paper draft.
import           Control.Monad (guard, foldM)
import           Control.Monad.RWS.Strict (RWS, ask, get, put, runRWS, tell)
import           Data.List (nub, intercalate)
import qualified Data.Map.Strict as M
import           Data.Maybe (fromMaybe)
import qualified Data.Set as S
import           System.Environment (getArgs)
import           System.IO (isEOF)

--------------------------------------------------------------------------------
-- Core data model: Facts, Disjunctions, Dependencies
--------------------------------------------------------------------------------

data Fact = Fact
  { fName  :: String
  , fArgs  :: [String]
  , fDeps  :: S.Set Dep
  , fProv  :: Maybe Provenance
  } deriving (Eq, Ord)

instance Show Fact where
  show (Fact n as deps prov)
    | S.null deps = n ++ show as ++ provStr
    | otherwise   = n ++ show as ++ "  ⟂ deps=" ++ show (S.toList deps) ++ provStr
    where provStr = maybe "" (("  ⟦" ++) . (++"⟧") . show) prov

data Disj = Disj
  { dId    :: Int
  , dAlts  :: [Fact]
  , dDeps  :: S.Set Dep
  , dProv  :: Maybe Provenance
  , dLabel :: Maybe String
  } deriving (Eq, Ord, Show)

type Dep = (Int, Int)

--------------------------------------------------------------------------------
-- Templates and matching up to renaming
--------------------------------------------------------------------------------

newtype Template = Template [Fact] deriving (Eq, Show)
type Subst = M.Map String String

isFixed :: String -> Bool; isFixed ('*':_) = True; isFixed _ = False
isWildcard :: String -> Bool; isWildcard ('?':_) = True; isWildcard _ = False

-- FINAL BUG FIX: The logic for matching fixed symbols was incorrect.
matchTemplate :: [Fact] -> Template -> Maybe Subst
matchTemplate facts (Template pats)
  | length facts /= length pats = Nothing
  | otherwise = go M.empty (zip facts pats)
  where
  go sigma [] = Just sigma
  go sigma ((Fact fn as _ _, Fact pn ps _ _):rest)
    | fn /= pn || length as /= length ps = Nothing
    | otherwise = case matchArgs sigma (zip as ps) of
        Nothing -> Nothing
        Just sigma' -> go sigma' rest

  matchArgs :: Subst -> [(String,String)] -> Maybe Subst
  matchArgs sigma [] = Just sigma
  matchArgs sigma ((a,p):xs)
    | isFixed p  = if a == drop 1 p then matchArgs sigma xs else Nothing -- Corrected
    | isWildcard p = Nothing
    | otherwise  = case M.lookup p sigma of
        Nothing -> matchArgs (M.insert p a sigma) xs
        Just a' | a' == a -> matchArgs sigma xs
                | otherwise -> Nothing

data Provenance = ProvHypothesis
                | ProvTheorem { thmName :: String, parentFacts :: [Fact], fromDisj :: Maybe (Int, Int), provSubs :: Maybe Subst }
                deriving (Eq, Ord, Show)

-- Structured trace events emitted by the prover (replace simple String logs)
data TraceEvent = TraceFactInserted { teThm :: String, teFact :: Fact, teParentDeps :: S.Set Dep, teParents :: [Fact], teSubs :: Subst }
                | TraceDisjInserted { teThm :: String, teDid :: Int, teLabel :: Maybe String, teAlts :: [Fact], teDeps :: S.Set Dep, teSubs :: Subst }
                deriving (Show)

-- Printing state for numbering and cross-references
data PrintState = PrintState { psMap :: M.Map String Int, psNext :: Int }

-- Prover monad: RWS over Engine (reader), log as [TraceEvent], and Env state
-- Top-level Prover helpers so they can be reused and tested
type ProverM = RWS Engine [TraceEvent] Env

-- Top-level Prover helpers so they can be reused and tested
insertFactM :: Fact -> ProverM Bool
insertFactM fact = do
  env <- get
  let (env', added) = insertFact fact env
  put env'
  if added
    then tell [TraceFactInserted { teThm = "(insert)", teFact = fact, teParentDeps = fDeps fact, teParents = [], teSubs = M.empty }]
    else pure ()
  pure added

insertDisjM :: Disj -> ProverM [Fact]
insertDisjM d = do
  env <- get
  let (env', alts) = insertDisj d env
  put env'
  let subs = case dProv d of
               Just (ProvTheorem { provSubs = m }) -> fromMaybe M.empty m
               _ -> M.empty
  tell [TraceDisjInserted { teThm = fromMaybe "(disj)" (dLabel d), teDid = dId d, teLabel = dLabel d, teAlts = dAlts d, teDeps = dDeps d, teSubs = subs }]
  pure alts

freshNameM :: String -> ProverM String
freshNameM prefix = do
  env <- get
  let (nm, env') = freshName prefix env
  put env'
  pure nm

materializeWildcardsM :: [Fact] -> ProverM [Fact]
materializeWildcardsM facts = do
  env <- get
  let (facts', env') = materializeWildcards facts env
  put env'
  pure facts'

processThmOutsM :: String -> ThmOut -> S.Set Dep -> [Fact] -> Subst -> ProverM ()
processThmOutsM thmNameParam thmOut parentDeps parents sigma =
  case thmOut of
    TOFact fact -> do
      facts' <- materializeWildcardsM [fact]
      let factWithProv = (head facts') { fDeps = parentDeps
                                       , fProv = Just (ProvTheorem { thmName = thmNameParam, parentFacts = parents, fromDisj = Nothing, provSubs = Just sigma }) }
      _ <- insertFactM factWithProv
      tell [TraceFactInserted { teThm = thmNameParam, teFact = factWithProv, teParentDeps = parentDeps, teParents = parents, teSubs = sigma }]
      pure ()

    TODisj alts -> do
      alts' <- materializeWildcardsM alts
      env <- get
      let label = Just $ thmNameParam ++ "(" ++ intercalate ", " (map (\ff -> fName ff ++ show (fArgs ff)) parents) ++ ")"
          disj = Disj { dId = eNextDid env
                      , dAlts = alts'
                      , dDeps = parentDeps
                      , dProv = Just (ProvTheorem { thmName = thmNameParam, parentFacts = parents, fromDisj = Nothing, provSubs = Just sigma })
                      , dLabel = label }
      _ <- insertDisjM disj
      -- increment did in state
      env' <- get
      put env' { eNextDid = eNextDid env' + 1 }
      tell [TraceDisjInserted { teThm = thmNameParam, teDid = dId disj, teLabel = dLabel disj, teAlts = dAlts disj, teDeps = dDeps disj, teSubs = sigma }]
      pure ()

stepRoundM :: ProverM ()
stepRoundM = do
   eng' <- ask
   env0' <- get
   if S.null (eFrontier env0')
     then put env0' { eFrontier = S.empty }
     else do
       -- compute applications from current env snapshot
       let factsList = S.toList (eFacts env0')
           runThm thm@Theorem{..} = do
             let Template pats = tTemplate
                 k = length pats
                 tuples = orderedTuples k factsList
             concatMap (\tuple -> case matchTemplate tuple tTemplate of
                                       Nothing -> []
                                       Just sigma -> let concreteTuple = map (substFact sigma) tuple
                                                         parentDeps = S.unions (map fDeps concreteTuple)
                                                         outputs = tApply concreteTuple
                                                     in map (\out -> (tName, out, parentDeps, concreteTuple, sigma)) outputs
                        ) tuples
       let applications = concatMap runThm (thms eng')
       -- apply each
       mapM_ (\(tname, out, pdeps, parents, sigma) -> processThmOutsM tname out pdeps parents sigma) applications
       -- update frontier
       envFinal <- get
       put envFinal { eFrontier = S.difference (eFacts envFinal) (eFacts env0') }
substFact :: Subst -> Fact -> Fact
substFact s (Fact n as deps prov) = Fact n (map sub as) deps prov
  where sub x | isFixed x = x | isWildcard x = x | otherwise = fromMaybe x (M.lookup x s)

--------------------------------------------------------------------------------
-- Prover environment
--------------------------------------------------------------------------------

data Env = Env
  { eFacts    :: S.Set Fact, eDisjs    :: M.Map Int Disj, eFrontier :: S.Set Fact
  , eNextDid  :: Int, eFresh    :: Int
  } deriving (Show)

emptyEnv :: Env; emptyEnv = Env S.empty M.empty S.empty 0 0

insertFact :: Fact -> Env -> (Env, Bool)
insertFact fact env@Env{..}
  | fact `S.member` eFacts = (env, False)
  | otherwise = ( env { eFacts = S.insert fact eFacts, eFrontier = S.insert fact eFrontier }, True)

insertDisj :: Disj -> Env -> (Env, [Fact])
insertDisj d@Disj{..} env0 = (env', alts')
  where
    env1 = env0 { eDisjs = M.insert dId d (eDisjs env0) }
    tagAlt ix f' =
      let altProv = case dProv of
                      Just (ProvTheorem { thmName = nm, parentFacts = pf, provSubs = ps }) -> Just (ProvTheorem { thmName = nm, parentFacts = pf, fromDisj = Just (dId, ix), provSubs = ps })
                      other -> other
      in f' { fDeps = S.unions [fDeps f', dDeps, S.singleton (dId, ix)], fProv = altProv }
    alts' = zipWith tagAlt [0..] dAlts
    (env', _) = foldl (\(e,_) f' -> insertFact f' e) (env1, False) alts'

freshName :: String -> Env -> (String, Env)
freshName prefix env@Env{..} = (prefix ++ show eFresh, env { eFresh = eFresh + 1 })

materializeWildcards :: [Fact] -> Env -> ([Fact], Env)
materializeWildcards facts env0 = (map subst facts, env')
  where
    (env', substs) = foldl step (env0, M.empty) (nub (concatMap fArgs facts))
    step (e, m) a | isWildcard a = let base = drop 1 a; (nm, e') = freshName (if null base then "X" else base ++ "_") e in (e', M.insert a nm m) | otherwise = (e, m)
    subst (Fact n as deps prov) = Fact n (map (\x -> M.findWithDefault x x substs) as) deps prov

--------------------------------------------------------------------------------
-- Theorems (Engine handles dependencies)
--------------------------------------------------------------------------------

data ThmOut = TOFact Fact | TODisj [Fact] deriving (Eq, Show)
data Theorem = Theorem { tName :: String, tTemplate :: Template, tApply :: [Fact] -> [ThmOut] }

f :: String -> [String] -> Fact; f n as = Fact n as S.empty Nothing

primesUpTo :: Integer -> [Integer]
primesUpTo n = sieve [2..n]
  where sieve [] = []
        sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

primeFactors :: Integer -> [Integer]
primeFactors n = go n (primesUpTo (limit :: Integer) ++ [n])
  where
    limit = floor (sqrt (fromIntegral n :: Double))
    go 1 _ = []
    go _ [] = []
    go m (p:ps) = if m `mod` p == 0 then p : go (m `div` p) (p:ps) else go m ps

uniq :: Ord a => [a] -> [a]; uniq = S.toList . S.fromList
allDivisors :: Integer -> [Integer]; allDivisors n = uniq $ map product (sequence [ [p^e | e <- [0..k]] | (p,k) <- run (primeFactors n)]) where run [] = []; run (x:xs) = let (same,rest) = span (==x) xs in (x, 1 + length same) : run rest
factorial :: Integer -> Integer; factorial m = product [1..m]

sylowTheorem :: Theorem
sylowTheorem = Theorem "SylowDivisibilityCongruence" (Template [ f "group" ["G"], f "order" ["G","n"] ])
  (\args -> case args of
      [_, Fact _ [_, nStr] _ _] ->
        let n = read nStr :: Integer
            ps = uniq (primeFactors n)
            mkDisj p = let ks = [k | k <- allDivisors n, k `mod` p == 1]; alts = [ f "numSylow" [show p, "G", show k] | k <- ks ]
                       in if null alts then TOFact (f "false" [])
                          else if length alts == 1 then TOFact (head alts) else TODisj alts
        in map mkDisj ps
      _ -> [])

uniqueSylowContradiction :: Theorem
uniqueSylowContradiction = Theorem "UniqueSylowImpliesNotSimple" (Template [ f "simple" ["G"], f "numSylow" ["p","G","*1"] ]) (\_ -> [TOFact (f "false" [])])

embedIntoAn :: Theorem
embedIntoAn = Theorem "EmbedIntoAlternatingViaSylowAction" (Template [ f "simple" ["G"], f "numSylow" ["p","G","m"] ])
  (\args -> case args of
      [_, Fact _ [_,_,m] _ _] -> let m' = read m :: Integer in if m' > 1 then [ TOFact (f "embedInAlt" ["G",m]) ] else []
      _ -> [])

orderDividesAlt :: Theorem
orderDividesAlt = Theorem "OrderMustDivideAlt" (Template [ f "embedInAlt" ["G","m"], f "order" ["G","n"] ])
  (\args -> case args of
      [Fact _ [_, mStr] _ _, Fact _ [_, nStr] _ _] ->
        let m = read mStr :: Integer
            n = read nStr :: Integer
            aOrder = factorial m `div` 2
        in if aOrder `mod` n /= 0 then [TOFact (f "false" [])] else []
      _ -> [])

--------------------------------------------------------------------------------
-- Proof engine
--------------------------------------------------------------------------------

data Engine = Engine { thms :: [Theorem], maxRounds :: Int, maxCaseSplit :: Int }
defaultEngine :: Engine
defaultEngine = Engine [ sylowTheorem, uniqueSylowContradiction, embedIntoAn, orderDividesAlt ] 50 12

-- Note: `stepRound` and its helpers are now implemented inside `runProver` using the RWS-based ProverM.

orderedTuples :: Int -> [a] -> [[a]]; orderedTuples 0 _ = [[]]; orderedTuples _ [] = []; orderedTuples k xs = [ x:ys | x <- xs, ys <- orderedTuples (k-1) xs ]

proved :: Engine -> Env -> Fact -> Bool
proved Engine{..} Env{..} goalPat =
  let instances = [ fct | fct <- S.toList eFacts, fName fct == fName goalPat, fArgs fct == fArgs goalPat]
      allDeps = S.unions (map fDeps instances)
      disjIds = S.toList (S.map fst allDeps)
      arities = map (\did -> (did, length (fromMaybe [] (fmap dAlts (M.lookup did eDisjs))))) disjIds
  in if any (\(_, arity) -> arity == 0) arities
       then True
       else if null disjIds
         then not (null instances) && any (S.null . fDeps) instances
         else if length disjIds > maxCaseSplit
           then False
           else let assignments = cartesian [ [ (did,ix) | ix <- [0..arity-1] ] | (did,arity) <- arities]
                    ok assign = any (\inst -> fDeps inst `S.isSubsetOf` S.fromList assign) instances
                in not (null instances) && not (null assignments) && all ok assignments

cartesian :: [[a]] -> [[a]]; cartesian [] = [[]]; cartesian (xs:xss) = [ x:ys | x <- xs, ys <- cartesian xss ]

--------------------------------------------------------------------------------
-- Running a proof
--------------------------------------------------------------------------------

runProver :: Engine -> [Fact] -> Fact -> IO (Bool, Env, [TraceEvent])
runProver eng hyps goal = do
  -- initialize env with hypotheses
  let env0 = foldl (\e h -> fst (insertFact (h { fProv = Just ProvHypothesis }) e)) emptyEnv hyps

  -- loop using runRWS to execute top-level stepRoundM repeatedly, accumulating logs
  let loopR 0 env acc = pure (False, env, acc)
      loopR i env acc =
        let ((), env', logs) = runRWS stepRoundM eng env
            acc' = acc ++ logs
        in if proved eng env' goal then pure (True, env', acc') else loopR (i-1) env' acc'

  loopR (maxRounds eng) env0 []

--------------------------------------------------------------------------------
-- Proof reconstruction & printing
--------------------------------------------------------------------------------

findGoalAssignments :: Engine -> Env -> Fact -> [[(Int,Int)]]
findGoalAssignments _eng env@Env{..} goalPat =
  let instances = [ fct | fct <- S.toList eFacts, fName fct == fName goalPat, fArgs fct == fArgs goalPat]
      allDeps = S.unions (map fDeps instances)
      disjIds = S.toList (S.map fst allDeps)
      arities = map (\did -> (did, length (fromMaybe [] (fmap dAlts (M.lookup did eDisjs))))) disjIds
  in if any (\(_, ar) -> ar == 0) arities then [[]]
     else if null disjIds then [[]]
     else let assignments = cartesian [ [ (did,ix) | ix <- [0..arity-1] ] | (did,arity) <- arities]
              ok assign = any (\inst -> fDeps inst `S.isSubsetOf` S.fromList assign) instances
          in filter ok assignments

findMatchingInstance :: Env -> Fact -> [(Int,Int)] -> Maybe Fact
findMatchingInstance Env{..} goalFact assign =
  let instances = [ fct | fct <- S.toList eFacts, fName fct == fName goalFact, fArgs fct == fArgs goalFact]
      assignSet = S.fromList assign
  in case [ i | i <- instances, fDeps i `S.isSubsetOf` assignSet ] of
       (x:_) -> Just x
       [] -> case instances of { (x:_) -> Just x; [] -> Nothing }

prettyPrintProof :: Engine -> Env -> Fact -> IO ()
prettyPrintProof eng env@Env{..} goalPat = do
  let assigns = findGoalAssignments eng env goalPat
  if null assigns
    then putStrLn "No proof assignments found."
    else do
      let assignsList = assigns
      _ <- foldM (\pst assign -> do
                   putStrLn "--- Case assignment ---"
                   let mapping = M.fromList assign
                   mapM_ (\(did, idx) -> do
                            case M.lookup did eDisjs of
                              Nothing -> putStrLn $ "disj " ++ show did ++ " -> " ++ show idx
                              Just Disj{..} -> do
                                case dLabel of
                                  Just lab -> putStrLn $ lab ++ " => chosen alt " ++ show idx
                                  Nothing  -> putStrLn $ "disjunction " ++ show did ++ " => chosen alt " ++ show idx
                                mapM_ (\(i,a) -> do
                                          -- determine whether choosing this alternative would also lead to a proof
                                          let assign' = map (\(x,y) -> if x == did then (x,i) else (x,y)) assign
                                              wouldWork = assign' `elem` assigns
                                              marker = if i == idx then "*" else " "
                                              status = if i == idx then "(chosen)" else if wouldWork then "(ok)" else "(fails)"
                                          putStrLn $ "  " ++ marker ++ "[" ++ show i ++ "] " ++ factPretty a ++ " " ++ status
                                       ) (zip [0..] dAlts)
                         ) (M.toList mapping)
                   putStrLn "Proof:";
                   case findMatchingInstance env goalPat assign of
                     Nothing -> putStrLn "  (no matching instance)" >> pure pst
                     Just inst -> do
                       pst' <- printFactRec' env inst assign 0 S.empty pst
                       pure pst'
                 ) (PrintState M.empty 1) assignsList
      pure ()
    

-- New variant: returns updated PrintState, assigns numbers to facts and prints cross-refs
printFactRec' :: Env -> Fact -> [(Int,Int)] -> Int -> S.Set String -> PrintState -> IO PrintState
printFactRec' env fact assign indent visited pst =
  let key = fName fact ++ show (fArgs fact) ++ show (S.toList (fDeps fact))
      pad n = replicate (n*2) ' '
  in case M.lookup key (psMap pst) of
       Just n -> do
         putStrLn $ pad indent ++ "(see #" ++ show n ++ ") " ++ factPretty fact
         pure pst
       Nothing -> do
         let myId = psNext pst
             pst' = pst { psMap = M.insert key myId (psMap pst), psNext = myId + 1 }
         putStrLn $ pad indent ++ "[" ++ show myId ++ "] " ++ factPretty fact
         case fProv fact of
           Nothing -> do
             -- try to infer provenance from disjunction deps
             let depsList = S.toList (fDeps fact)
             case depsList of
               ((did, idx):_) -> case M.lookup did (eDisjs env) of
                 Just Disj{..} -> case dProv of
                   Just (ProvTheorem { thmName = nm, parentFacts = parents, provSubs = subs }) -> do
                     let subsStr = case subs of
                                     Nothing -> ""
                                     Just s -> "  {" ++ intercalate ", " (map (\(k,v) -> k ++ " := " ++ v) (M.toList s)) ++ "}"
                     putStrLn $ pad indent ++ "  — by " ++ nm ++ subsStr ++ " (from disjunction " ++ fromMaybe (show did) dLabel ++ ", alt " ++ show idx ++ ")"
                     let visited' = S.insert key visited
                     foldM (\uacc p -> do
                              case findMatchingInstance env p assign of
                                Just par -> printFactRec' env par assign (indent+1) visited' uacc
                                Nothing -> do
                                  putStrLn $ pad (indent+1) ++ "(missing parent) " ++ factPretty p
                                  pure uacc
                           ) pst' parents
                   _ -> do
                     putStrLn $ pad indent ++ "  — by unknown provenance"
                     pure pst'
                 Nothing -> do
                   putStrLn $ pad indent ++ "  — by unknown provenance"
                   pure pst'
               [] -> do
                 putStrLn $ pad indent ++ "  — by unknown provenance"
                 pure pst'
           Just ProvHypothesis -> do
             putStrLn $ pad indent ++ "  — hypothesis"
             pure pst'
           Just (ProvTheorem { thmName = nm, parentFacts = parents, fromDisj = _, provSubs = subs }) -> do
             let subsStr = case subs of
                             Nothing -> ""
                             Just s -> "  {" ++ intercalate ", " (map (\(k,v) -> k ++ " := " ++ v) (M.toList s)) ++ "}"
             putStrLn $ pad indent ++ "  — by " ++ nm ++ subsStr ++ " (from: " ++ intercalate ", " (map factPretty parents) ++ ")"
             let visited' = S.insert key visited
             -- fold parents threading the PrintState
             foldM (\uacc p -> do
                      case findMatchingInstance env p assign of
                        Just par -> printFactRec' env par assign (indent+1) visited' uacc
                        Nothing -> do
                          putStrLn $ pad (indent+1) ++ "(missing parent) " ++ factPretty p
                          pure uacc
                   ) pst' parents

factPretty :: Fact -> String
factPretty (Fact n as _ _) = n ++ "(" ++ intercalate ", " as ++ ")"

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

hypotheses :: Integer -> [Fact]
hypotheses n = [ f "group" ["G"], f "order" ["G", show n], f "simple" ["G"] ]

goalFalse :: Fact; goalFalse = f "false" []

example :: Integer -> IO ()
example n = do
  putStrLn $ "Attempting: no simple group of order " ++ show n
  (ok, env, _trace) <- runProver defaultEngine (hypotheses n) goalFalse
  if ok
    then do
      putStrLn "✓ CONTRADICTION derived (goal proven)."
      prettyPrintProof defaultEngine env goalFalse
    else putStrLn "✗ Could not derive contradiction."

main :: IO ()
main = do
  args <- getArgs
  case args of
    (a:_) -> let n = read a :: Integer in example n
    _ -> do
      -- If there's data on stdin, read the first line as the order to attempt.
      hasStdin <- isEOF
      if not hasStdin
        then do
          line <- getLine
          case reads line :: [(Integer, String)] of
            ((n,_):_) -> example n
            _ -> putStrLn $ "Invalid input on stdin: " ++ line
        else do
          example 40
          putStrLn ""
          example 24
