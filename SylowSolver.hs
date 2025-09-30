{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE RecordWildCards #-}
-- A tiny, extensible Sylow-based theorem prover prototype in Haskell
-- Implements the "facts + techniques (theorems) + proof search with disjunction dependencies"
-- architecture from the provided paper draft.

module Main where

import           Control.Monad (guard)
import           Data.List (nub)
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
  } deriving (Eq, Ord)

instance Show Fact where
  show (Fact n as deps)
    | S.null deps = n ++ show as
    | otherwise   = n ++ show as ++ "  ⟂ deps=" ++ show (S.toList deps)

data Disj = Disj
  { dId    :: Int
  , dAlts  :: [Fact]
  , dDeps  :: S.Set Dep
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
    go sigma ((Fact fn as _, Fact pn ps _):rest)
      | fn /= pn || length as /= length ps = Nothing
      | otherwise = case matchArgs sigma (zip as ps) of
          Nothing -> Nothing; Just sigma' -> go sigma' rest
    matchArgs :: Subst -> [(String,String)] -> Maybe Subst
    matchArgs sigma [] = Just sigma
    matchArgs sigma ((a,p):xs)
      | isFixed p  = if a == drop 1 p then matchArgs sigma xs else Nothing -- Corrected
      | isWildcard p = Nothing
      | otherwise  = case M.lookup p sigma of
          Nothing -> matchArgs (M.insert p a sigma) xs
          Just a' | a' == a -> matchArgs sigma xs | otherwise -> Nothing

substFact :: Subst -> Fact -> Fact
substFact s (Fact n as deps) = Fact n (map sub as) deps
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
    tagAlt ix f' = f' { fDeps = S.unions [fDeps f', dDeps, S.singleton (dId, ix)] }
    alts' = zipWith tagAlt [0..] dAlts
    (env', _) = foldl (\(e,_) f' -> insertFact f' e) (env1, False) alts'

freshName :: String -> Env -> (String, Env)
freshName prefix env@Env{..} = (prefix ++ show eFresh, env { eFresh = eFresh + 1 })

materializeWildcards :: [Fact] -> Env -> ([Fact], Env)
materializeWildcards facts env0 = (map subst facts, env')
  where
    (env', substs) = foldl step (env0, M.empty) (nub (concatMap fArgs facts))
    step (e, m) a | isWildcard a = let base = drop 1 a; (nm, e') = freshName (if null base then "X" else base ++ "_") e in (e', M.insert a nm m) | otherwise = (e, m)
    subst (Fact n as deps) = Fact n (map (\x -> M.findWithDefault x x substs) as) deps

--------------------------------------------------------------------------------
-- Theorems (Engine handles dependencies)
--------------------------------------------------------------------------------

data ThmOut = TOFact Fact | TODisj [Fact] deriving (Eq, Show)
data Theorem = Theorem { tName :: String, tTemplate :: Template, tApply :: [Fact] -> [ThmOut] }
f :: String -> [String] -> Fact; f n as = Fact n as S.empty

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
      [_, Fact _ [_, nStr] _] ->
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
      [_, Fact _ [_,_,m] _] -> let m' = read m :: Integer in if m' > 1 then [ TOFact (f "embedInAlt" ["G",m]) ] else []
      _ -> [])

orderDividesAlt :: Theorem
orderDividesAlt = Theorem "OrderMustDivideAlt" (Template [ f "embedInAlt" ["G","m"], f "order" ["G","n"] ])
  (\args -> case args of
      [Fact _ [_, mStr] _, Fact _ [_, nStr] _] ->
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

stepRound :: Engine -> Env -> Env
stepRound Engine{..} env0
  | S.null (eFrontier env0) = env0 { eFrontier = S.empty }
  | otherwise = let envFinal = foldl applyThmForEnv env0 { eFrontier = S.empty } thms
                in envFinal { eFrontier = S.difference (eFacts envFinal) (eFacts env0) }
  where
    applyThmForEnv env Theorem{..} =
      let applications = do
            let Template pats = tTemplate
                k = length pats
                factsList = S.toList (eFacts env0)
            tuple <- orderedTuples k factsList
            guard (any (`S.member` (eFrontier env0)) tuple)
            case matchTemplate tuple tTemplate of
              Nothing -> []
              Just sigma ->
                let concreteTuple = map (substFact sigma) tuple
                    parentDeps = S.unions (map fDeps concreteTuple)
                    outputs = tApply concreteTuple
                in return (outputs, parentDeps)
      in foldl (\acc_env (outs, pDeps) -> foldl (\e o -> processThmOuts e o pDeps) acc_env outs) env applications

    processThmOuts :: Env -> ThmOut -> S.Set Dep -> Env
    processThmOuts env (TOFact fact) parentDeps =
      let (facts', env') = materializeWildcards [fact] env
      in fst $ insertFact (head facts') { fDeps = parentDeps } env'
    processThmOuts env (TODisj alts) parentDeps =
      let (alts', env') = materializeWildcards alts env
          disj = Disj { dId = eNextDid env', dAlts = alts', dDeps = parentDeps }
          env_with_inc_did = env' { eNextDid = eNextDid env' + 1 }
      in fst $ insertDisj disj env_with_inc_did

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

runProver :: Engine -> [Fact] -> Fact -> IO (Bool, Env)
runProver eng hyps goal = do
  let env0 = foldl (\e h -> fst (insertFact h e)) emptyEnv hyps
  loop 0 env0
  where
    loop i env
      | proved eng env goal = pure (True, env)
      | i >= maxRounds eng  = pure (False, env)
      | otherwise = loop (i+1) (stepRound eng env)

--------------------------------------------------------------------------------
-- Examples
--------------------------------------------------------------------------------

hypotheses :: Integer -> [Fact]
hypotheses n = [ f "group" ["G"], f "order" ["G", show n], f "simple" ["G"] ]

goalFalse :: Fact; goalFalse = f "false" []

example :: Integer -> IO ()
example n = do
  putStrLn $ "Attempting: no simple group of order " ++ show n
  (ok, _) <- runProver defaultEngine (hypotheses n) goalFalse
  putStrLn $ if ok then "✓ CONTRADICTION derived (goal proven)." else "✗ Could not derive contradiction."

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
