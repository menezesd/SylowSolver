module Env
  ( FactEntry(..)
  , DisjunctionEntry(..)
  , Labeled(..)
  , ProofEnvironment(..)
  , NewConclusion(..)
  , initEnv
  , addNewFacts
  , applyThm
  , updateGoalAchieved
  , updateUseful
  , factEquals
  ) where

import Core
import DisjunctionHash (disjLabelNumber)
import Data.List (intercalate, sort)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Set (Set)
import qualified Data.Set as Set

data FactEntry = FactEntry
  { feFact :: Fact
  , feLabel :: FactId
  , feDependencies :: [Label]
  , feDisAncestors :: Set (DisjId, Int)
  , feConcThm :: Maybe String
  , feUseful :: Bool
  , feDepth :: Int
  } deriving (Eq, Show)

data DisjunctionEntry = DisjunctionEntry
  { deFacts :: [Fact]
  , deLabel :: DisjId
  , deDependencies :: [Label]
  , deDisAncestors :: Set (DisjId, Int)
  , deConcThm :: Maybe String
  , deUseful :: Bool
  } deriving (Eq, Show)

data Labeled
  = LFactEntry FactEntry
  | LDisjEntry DisjunctionEntry
  deriving (Eq, Show)

data ProofEnvironment = ProofEnvironment
  { peOrderedFacts :: [Label]
  , peFacts :: [FactEntry]
  , peTheorems :: [Thm]
  , peThmNameDict :: Map String Thm
  , peDisjunctions :: [DisjunctionEntry]
  , peGoal :: Fact
  , peGoalAchieved :: Bool
  , peGoalDisCombos :: [Set (DisjId, Int)]
  , peFactLabels :: Map Label Labeled
  , peCurFactNum :: Int
  , peCurLetter :: Char
  , peCurSuffix :: Int
  , peCaseDepth :: Int
  , peNumCases :: Int
  , peSolvedCases :: Int
  , peCaseDis :: Maybe DisjunctionEntry
  , peCaseFact :: Maybe FactEntry
  , peSymbolSet :: Set String
  }

data NewConclusion = NewConclusion
  { ncConclusion :: Conclusion
  , ncDependencies :: [Label]
  , ncDisAncestors :: Set (DisjId, Int)
  , ncConcThm :: Maybe String
  }

initEnv :: [Fact] -> [Thm] -> Map String Thm -> Fact -> ProofEnvironment
initEnv facts theorems thmDict goal =
  let base =
        ProofEnvironment
          { peOrderedFacts = []
          , peFacts = []
          , peTheorems = theorems
          , peThmNameDict = thmDict
          , peDisjunctions = []
          , peGoal = goal
          , peGoalAchieved = False
          , peGoalDisCombos = []
          , peFactLabels = Map.empty
          , peCurFactNum = 0
          , peCurLetter = 'A'
          , peCurSuffix = 0
          , peCaseDepth = 0
          , peNumCases = 0
          , peSolvedCases = 0
          , peCaseDis = Nothing
          , peCaseFact = Nothing
          , peSymbolSet = Set.empty
          }
      initialConcs =
        [ NewConclusion (CFact f) [] Set.empty Nothing | f <- facts
        ]
      (envWithFacts, _) = addNewFacts base initialConcs
      initialSymbols =
        Set.fromList
          [ argText arg | Fact _ args <- facts, arg <- args ]
   in envWithFacts {peSymbolSet = initialSymbols}

factEquals :: Fact -> Fact -> Bool
factEquals a b = factName a == factName b && factArgs a == factArgs b

newLabel :: ProofEnvironment -> (ProofEnvironment, FactId)
newLabel env =
  let lbl = FactId (peCurFactNum env)
   in (env {peCurFactNum = peCurFactNum env + 1}, lbl)

canonicalDisjunctionSignature :: DisjunctionEntry -> String
canonicalDisjunctionSignature disj =
  let sigs =
        sort
          [ factName f ++ ":" ++ intercalate "," (map argText (factArgs f))
          | f <- deFacts disj
          ]
      prov =
        concat
          [ case deConcThm disj of
              Nothing -> []
              Just n -> ["thm:" ++ n]
          , if Set.null (deDisAncestors disj)
              then []
              else
                let ancLabels = sort (Set.toList (Set.map disjLabelText (deDisAncestors disj)))
                 in ["anc:" ++ intercalate "," ancLabels]
          ]
   in if null prov then intercalate "|" sigs else intercalate "|" sigs ++ "::" ++ intercalate "|" prov

disjLabelText :: (DisjId, Int) -> String
disjLabelText (DisjId n, _) = "D" ++ show n

newDisjunctionLabel :: ProofEnvironment -> DisjunctionEntry -> DisjId
newDisjunctionLabel env disj =
  let canon = canonicalDisjunctionSignature disj
      num = disjLabelNumber canon
      probeLabel p = DisjId ((num + p) `mod` 1000000)
      loop p =
        let lbl = probeLabel p
         in case Map.lookup (LDisj lbl) (peFactLabels env) of
              Nothing -> lbl
              Just (LDisjEntry existing)
                | canonicalDisjunctionSignature existing == canon -> lbl
                | otherwise -> loop (p + 1)
              _ -> loop (p + 1)
   in loop 0

updateGoalAchieved :: ProofEnvironment -> ProofEnvironment
updateGoalAchieved env =
  if null (peGoalDisCombos env)
    then env
    else
      let fullDisSet = Set.unions (peGoalDisCombos env)
          disLabels = Set.toList (Set.map fst fullDisSet)
          disSizes =
            [ (d, length facts)
            | d <- disLabels
            , Just (LDisjEntry disj) <- [Map.lookup (LDisj d) (peFactLabels env)]
            , let facts = deFacts disj
            ]
          cartesian [] = [[]]
          cartesian (xs : xss) = [x : ys | x <- xs, ys <- cartesian xss]
          domain =
            [ [ (d, i) | i <- [0 .. l - 1] ]
            | (d, l) <- disSizes
            ]
          fullCombos = map Set.fromList (cartesian domain)
          observed = peGoalDisCombos env
          covered s = any (`Set.isSubsetOf` s) observed
          allCovered = all covered fullCombos
       in if allCovered then env {peGoalAchieved = True} else env

updateUseful :: Label -> ProofEnvironment -> ProofEnvironment
updateUseful lbl env =
  case Map.lookup lbl (peFactLabels env) of
    Just (LFactEntry fe)
      | feUseful fe -> env
      | otherwise ->
          let fe' = fe {feUseful = True}
              env' = env {peFactLabels = Map.insert lbl (LFactEntry fe') (peFactLabels env)}
           in foldl (flip updateUseful) env' (feDependencies fe)
    _ -> env

replaceVariables :: ProofEnvironment -> [NewConclusion] -> (ProofEnvironment, [NewConclusion])
replaceVariables env concs =
  let (env', subst) = buildSubst env concs Map.empty
      applyFact f =
        let args = map (replaceArg subst) (factArgs f)
         in f {factArgs = args}
      applyConclusion (CFact f) = CFact (applyFact f)
      applyConclusion (CDisj (Disjunction facts)) =
        CDisj (Disjunction (map applyFact facts))
      concs' =
        [ nc {ncConclusion = applyConclusion (ncConclusion nc)} | nc <- concs
        ]
   in (env', concs')
  where
    replaceArg subst arg =
      case arg of
        Fresh name ->
          case Map.lookup name subst of
            Just symName -> Sym symName
            Nothing -> arg
        _ -> arg
    buildSubst env' [] subst = (env', subst)
    buildSubst env' (nc : rest) subst =
      let facts =
            case ncConclusion nc of
              CFact f -> [f]
              CDisj (Disjunction fs) -> fs
          (env'', subst') = foldl (assignVar env') (env', subst) facts
       in buildSubst env'' rest subst'
    assignVar env' (envAcc, subst) (Fact _ args) =
      foldl (assignArg env') (envAcc, subst) args
    assignArg env' (envAcc, subst) arg
      | otherwise =
          case arg of
            Fresh name ->
              case Map.lookup name subst of
                Just _ -> (envAcc, subst)
                Nothing ->
                  let (envNext, symName) = generateNewSymbol envAcc
                   in (envNext, Map.insert name symName subst)
            _ -> (envAcc, subst)

generateNewSymbol :: ProofEnvironment -> (ProofEnvironment, String)
generateNewSymbol env =
  let go curLetter curSuffix =
        let suffix = if curSuffix == 0 then "" else show curSuffix
            sym = curLetter : suffix
            nextLetter = if curLetter == 'Z' then 'A' else succ curLetter
            nextSuffix = if curLetter == 'Z' then curSuffix + 1 else curSuffix
         in if Set.member sym (peSymbolSet env)
              then go nextLetter nextSuffix
              else
                ( env
                    { peCurLetter = nextLetter
                    , peCurSuffix = nextSuffix
                    , peSymbolSet = Set.insert sym (peSymbolSet env)
                    }
                , sym
                )
   in go (peCurLetter env) (peCurSuffix env)

applyThm :: ProofEnvironment -> Thm -> [FactEntry] -> (ProofEnvironment, [FactEntry])
applyThm env thm facts =
  let usedAnc = Set.unions (map feDisAncestors facts)
      usedDict = Map.fromList (Set.toList usedAnc)
      consistent = all (\(d, i) -> Map.lookup d usedDict == Just i) (Set.toList usedAnc)
   in if not consistent
        then (env, [])
        else
          let concs =
                case thm of
                  Std t -> map CFact (applyStdThm t facts)
                  Hyper t -> hyperRule t (map feFact facts)
              deps = map (LFact . feLabel) facts
              nc =
                [ NewConclusion c deps usedAnc (Just (thmName thm))
                | c <- concs
                ]
              (env', nc') = replaceVariables env nc
              (env'', newEntries) = addNewFacts env' nc'
           in (env'', newEntries)

applyStdThm :: Theorem -> [FactEntry] -> [Fact]
applyStdThm thm facts =
  case unifyTheoremFacts (theoremFacts thm) (map feFact facts) of
    Nothing -> []
    Just mapping -> map (substFact mapping) (theoremConcs thm)
  where
    substFact mapping (Fact name args) =
      let args' = map (substArg mapping) args
       in Fact name args'
    substArg mapping arg =
      case arg of
        Var name ->
          case Map.lookup name mapping of
            Just symName -> Sym symName
            Nothing -> arg
        Exact name ->
          case Map.lookup name mapping of
            Just symName -> Sym symName
            Nothing -> Sym name
        _ -> arg

unifyTheoremFacts :: [Fact] -> [Fact] -> Maybe (Map String String)
unifyTheoremFacts tFacts fFacts = go Map.empty tFacts fFacts
  where
    go mapping [] [] = Just mapping
    go mapping (t : ts) (f : fs) = do
      mapping' <- unifyFact mapping t f
      go mapping' ts fs
    go _ _ _ = Nothing

unifyFact :: Map String String -> Fact -> Fact -> Maybe (Map String String)
unifyFact mapping (Fact tName tArgs) (Fact fName fArgs)
  | tName /= fName = Nothing
  | length tArgs /= length fArgs = Nothing
  | otherwise = foldl step (Just mapping) (zip tArgs fArgs)
  where
    step acc (tArg, fArg) = do
      m <- acc
      case tArg of
        Exact name ->
          if name == argText fArg then Just m else Nothing
        Var name ->
          case Map.lookup name m of
            Nothing -> Just (Map.insert name (argText fArg) m)
            Just v -> if v == argText fArg then Just m else Nothing
        Sym name ->
          if name == argText fArg then Just m else Nothing
        Fresh name ->
          case Map.lookup name m of
            Nothing -> Just (Map.insert name (argText fArg) m)
            Just v -> if v == argText fArg then Just m else Nothing

addNewFacts :: ProofEnvironment -> [NewConclusion] -> (ProofEnvironment, [FactEntry])
addNewFacts env concs = foldl addOne (env, []) concs
  where
    addOne (acc, added) nc =
      case ncConclusion nc of
        CFact f ->
          let (acc', newFacts) = addFact acc nc f
           in (acc', added ++ newFacts)
        CDisj (Disjunction fs) ->
          let (acc', newFacts) = addDisjunction acc nc fs
           in (acc', added ++ newFacts)

    addFact acc nc f =
      let (acc', lbl) = newLabel acc
          symbols' =
            Set.union
              (peSymbolSet acc')
              (Set.fromList (map argText (factArgs f)))
          entry =
            FactEntry
              { feFact = f
              , feLabel = lbl
              , feDependencies = ncDependencies nc
              , feDisAncestors = ncDisAncestors nc
              , feConcThm = ncConcThm nc
              , feUseful = False
              , feDepth = peCaseDepth acc'
              }
          labels' = Map.insert (LFact lbl) (LFactEntry entry) (peFactLabels acc')
          facts' = entry : peFacts acc'
          ordered' = peOrderedFacts acc' ++ [LFact lbl]
          acc'' =
            acc'
              { peFactLabels = labels'
              , peFacts = facts'
              , peOrderedFacts = ordered'
              , peSymbolSet = symbols'
              }
          accGoal =
            if factEquals f (peGoal acc'')
              then
                let accG =
                      acc''
                        { peGoalDisCombos =
                            ncDisAncestors nc : peGoalDisCombos acc''
                        }
                    accG' = updateUseful (LFact lbl) accG
                 in updateGoalAchieved accG'
              else acc''
       in (accGoal, [entry])

    addDisjunction acc nc fs =
      let disj =
            DisjunctionEntry
              { deFacts = fs
              , deLabel = DisjId 0
              , deDependencies = ncDependencies nc
              , deDisAncestors = ncDisAncestors nc
              , deConcThm = ncConcThm nc
              , deUseful = False
              }
          lbl = newDisjunctionLabel acc disj
          disj' = disj {deLabel = lbl}
          labels' = Map.insert (LDisj lbl) (LDisjEntry disj') (peFactLabels acc)
          ordered' = peOrderedFacts acc ++ [LDisj lbl]
          acc' =
            acc
              { peFactLabels = labels'
              , peDisjunctions = disj' : peDisjunctions acc
              , peOrderedFacts = ordered'
              }
          subConcs =
            [ NewConclusion (CFact f) [LDisj lbl] (Set.insert (lbl, i) (deDisAncestors disj')) (ncConcThm nc)
            | (i, f) <- zip [0 ..] fs
            ]
       in addNewFacts acc' subConcs
