-- | Tree-structured proof output for cleaner visualization.
--
-- This module builds a hierarchical tree from the proof trace, grouping facts
-- by their case context (disjunction branches). It provides both a cleaner
-- linear output (Option B) and a tree visualization (Option D).
module ProofTree
  ( ProofTree(..)
  , CaseBranch(..)
  , buildProofTree
  , renderTree
  , renderClean
  ) where

import Core (Fact(..), Label(..), DisjId(..), FactId(..), TheoremName, PredName(..)
            , theoremNameText, factName)
import Environment.Symbols (SymbolTable, symbolTable, ppFactWithSymbols)
import Environment.Types (ProofEnvironment, FactEntry(..), DisjMeta(..)
                         , feDisAncestors, feConcThm, feDependencies, peDisjMeta, peFacts)
import Data.List (intercalate, sortOn)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set

-- | A branch in a case split
data CaseBranch = CaseBranch
  { cbDisjId :: DisjId
  , cbBranchIdx :: Int
  , cbLabel :: String      -- e.g., "n₂ = 1"
  , cbChildren :: ProofTree
  } deriving (Show)

-- | Tree structure for proof
data ProofTree
  = PTEmpty
  | PTFact FactInfo ProofTree          -- A single fact followed by more
  | PTCaseSplit DisjId String [CaseBranch]  -- Disjunction with var name and branches
  | PTContradiction String             -- Reached false() with explanation
  deriving (Show)

-- | Simplified fact info for display
data FactInfo = FactInfo
  { fiLabel :: FactId
  , fiFact :: Fact
  , fiTheorem :: Maybe TheoremName
  , fiDeps :: [Label]
  } deriving (Show)

-- | Build a proof tree from the environment (filtered to essential facts)
buildProofTree :: ProofEnvironment -> ProofTree
buildProofTree env =
  let facts = reverse (peFacts env)  -- Chronological order
      metaMap = peDisjMeta env
      symTbl = symbolTable env

      -- Build lookup map and find essential facts
      factMap = IntMap.fromList [(unFactId (feLabel fe), fe) | fe <- facts]
      contradictions = [fe | fe <- facts, factName (feFact fe) == PFalse]
      essentialIds = Set.unions [traceEssential factMap (feLabel fe) | fe <- contradictions]
      essential = deduplicateFacts [fe | fe <- facts, Set.member (feLabel fe) essentialIds]

   in buildTree metaMap symTbl Set.empty essential

-- Build tree recursively, grouping by case context
buildTree :: IntMap.IntMap DisjMeta -> SymbolTable -> Set.Set (DisjId, Int) -> [FactEntry] -> ProofTree
buildTree _ _ _ [] = PTEmpty
buildTree metaMap tbl currentCase allFacts =
  let (matching, rest) = extractMatchingFacts currentCase allFacts
      factInfos = map toFactInfo matching
   in if hasContradiction factInfos
        then buildContradictionBranch factInfos
        else buildNormalBranch metaMap tbl currentCase factInfos rest

-- | Extract facts matching the current case context exactly
{-# INLINE extractMatchingFacts #-}
extractMatchingFacts :: Set.Set (DisjId, Int) -> [FactEntry] -> ([FactEntry], [FactEntry])
extractMatchingFacts currentCase = span (\fe -> feDisAncestors fe == currentCase)

-- | Convert a FactEntry to FactInfo for display
{-# INLINE toFactInfo #-}
toFactInfo :: FactEntry -> FactInfo
toFactInfo fe = FactInfo (feLabel fe) (feFact fe) (feConcThm fe) (feDependencies fe)

-- | Check if any fact is a contradiction (false)
{-# INLINE hasContradiction #-}
hasContradiction :: [FactInfo] -> Bool
hasContradiction = any (\fi -> factName (fiFact fi) == PFalse)

-- | Build a branch that ends in contradiction
buildContradictionBranch :: [FactInfo] -> ProofTree
buildContradictionBranch [] = PTEmpty
buildContradictionBranch fis = foldr PTFact (PTContradiction "contradiction") (init fis)

-- | Build a normal branch (possibly with case splits)
buildNormalBranch :: IntMap.IntMap DisjMeta -> SymbolTable
                  -> Set.Set (DisjId, Int) -> [FactInfo] -> [FactEntry] -> ProofTree
buildNormalBranch metaMap tbl currentCase factInfos rest =
  case findNextSplit currentCase rest of
    Nothing -> foldr PTFact PTEmpty factInfos
    Just (disjId, _) ->
      let caseBranches = buildCaseBranches metaMap tbl currentCase rest disjId
       in foldr PTFact (PTCaseSplit disjId (getVarName metaMap disjId) caseBranches) factInfos

-- | Get variable name from disjunction metadata
getVarName :: IntMap.IntMap DisjMeta -> DisjId -> String
getVarName metaMap disjId =
  case IntMap.lookup (unDisjId disjId) metaMap of
    Just meta -> dmVarName meta
    Nothing -> "case"

-- | Get branch values from disjunction metadata
getBranchValues :: IntMap.IntMap DisjMeta -> DisjId -> [String]
getBranchValues metaMap disjId =
  case IntMap.lookup (unDisjId disjId) metaMap of
    Just meta -> dmBranchValues meta
    Nothing -> map show [(0::Int)..]

-- | Build all case branches for a disjunction
buildCaseBranches :: IntMap.IntMap DisjMeta -> SymbolTable
                  -> Set.Set (DisjId, Int) -> [FactEntry] -> DisjId -> [CaseBranch]
buildCaseBranches metaMap tbl currentCase rest disjId =
  [ CaseBranch disjId idx label subtree
  | (idx, label) <- zip [0..] (getBranchValues metaMap disjId)
  , let newCase = Set.insert (disjId, idx) currentCase
        branchFacts = filter (\fe -> Set.isSubsetOf newCase (feDisAncestors fe)) rest
        subtree = buildTree metaMap tbl newCase branchFacts
  ]

-- | Find the next case split point
findNextSplit :: Set.Set (DisjId, Int) -> [FactEntry] -> Maybe (DisjId, [Int])
findNextSplit currentCase facts =
  case findExtensions currentCase facts of
    [] -> Nothing
    ((d, _) : exts) ->
      let branches = Set.toList $ Set.fromList [i | (d', i) <- (d, 0) : exts, d' == d]
       in Just (d, branches)

-- | Find disjunction extensions beyond current case
findExtensions :: Set.Set (DisjId, Int) -> [FactEntry] -> [(DisjId, Int)]
findExtensions currentCase facts =
  [ (d, i)
  | fe <- facts
  , (d, i) <- Set.toList (Set.difference (feDisAncestors fe) currentCase)
  ]

-- | Render the tree as ASCII art
renderTree :: ProofEnvironment -> [String]
renderTree env =
  let tree = buildProofTree env
      metaMap = peDisjMeta env
      symTbl = symbolTable env
      facts = reverse (peFacts env)
      contradictions = [fe | fe <- facts, factName (feFact fe) == PFalse]
      summary = renderSummary metaMap contradictions
   in ["", "Proof Structure:", "════════════════", ""]
      ++ renderNode symTbl metaMap "" tree
      ++ summary

renderNode :: SymbolTable -> IntMap.IntMap DisjMeta -> String -> ProofTree -> [String]
renderNode _ _ _ PTEmpty = []
renderNode _tbl _meta prefix (PTContradiction _) = [prefix ++ "└─ ⊥ (contradiction)"]
renderNode tbl meta prefix (PTFact fi rest) =
  let factStr = ppFactWithSymbols tbl (fiFact fi)
      labelStr = "F" ++ show (unFactId (fiLabel fi))
      thmStr = case fiTheorem fi of
                 Just tn -> " [" ++ theoremNameText tn ++ "]"
                 Nothing -> " [hypothesis]"
   in (prefix ++ "• " ++ labelStr ++ ": " ++ factStr ++ thmStr) : renderNode tbl meta prefix rest
renderNode tbl meta prefix (PTCaseSplit _disjId varName branches) =
  let header = prefix ++ "┌─ Case split on " ++ varName ++ ":"
   in header : concatMap (renderBranch tbl meta prefix (length branches)) (zip [0..] branches)

renderBranch :: SymbolTable -> IntMap.IntMap DisjMeta -> String -> Int -> (Int, CaseBranch) -> [String]
renderBranch tbl meta prefix total (idx, branch) =
  let isLast = idx == total - 1
      connector = if isLast then "└" else "├"
      childPrefix = if isLast then prefix ++ "  " else prefix ++ "│ "
      branchHeader = prefix ++ connector ++ "─ " ++ cbLabel branch ++ ":"
   in branchHeader : renderNode tbl meta childPrefix (cbChildren branch)

-- | Render cleaner linear output with improvements:
--   1. Filter to essential facts only (trace back from false())
--   2. Group by case context with headers
--   3. Add proof summary showing closed branches
--   4. Highlight contradictions
renderClean :: ProofEnvironment -> [String]
renderClean env =
  let facts = reverse (peFacts env)  -- Chronological order
      metaMap = peDisjMeta env
      symTbl = symbolTable env

      -- Build lookup map from FactId -> FactEntry
      factMap = IntMap.fromList [(unFactId (feLabel fe), fe) | fe <- facts]

      -- Find all false() facts (contradictions)
      contradictions = [fe | fe <- facts, factName (feFact fe) == PFalse]

      -- Trace back to find essential facts
      essentialIds = Set.unions [traceEssential factMap (feLabel fe) | fe <- contradictions]
      essential = [fe | fe <- facts, Set.member (feLabel fe) essentialIds]

      -- Deduplicate
      deduped = deduplicateFacts essential

      -- Group by case context
      grouped = groupByCaseContext deduped

      -- Render each group
      renderedGroups = concatMap (renderCaseGroup symTbl metaMap) grouped

      -- Build summary
      summary = renderSummary metaMap contradictions

   in renderedGroups ++ summary

-- Trace back through dependencies to find all essential facts
traceEssential :: IntMap.IntMap FactEntry -> FactId -> Set.Set FactId
traceEssential factMap startId = go Set.empty [startId]
  where
    go visited [] = visited
    go visited (fid:rest)
      | Set.member fid visited = go visited rest
      | otherwise = case IntMap.lookup (unFactId fid) factMap of
          Nothing -> go visited rest
          Just fe ->
            let depIds = [did | LFact did <- feDependencies fe]
             in go (Set.insert fid visited) (depIds ++ rest)

-- Deduplicate facts by (fact content, case context) while preserving order
deduplicateFacts :: [FactEntry] -> [FactEntry]
deduplicateFacts = go Set.empty
  where
    go _ [] = []
    go seen (fe:fes) =
      let key = (feFact fe, feDisAncestors fe)
       in if Set.member key seen
            then go seen fes
            else fe : go (Set.insert key seen) fes

-- Group facts by their case context
groupByCaseContext :: [FactEntry] -> [(Set.Set (DisjId, Int), [FactEntry])]
groupByCaseContext facts =
  let -- Get all unique case contexts, sorted by size (hypotheses first)
      contexts = Set.toList $ Set.fromList [feDisAncestors fe | fe <- facts]
      sortedContexts = sortOn Set.size contexts
      -- Group facts by context
   in [(ctx, [fe | fe <- facts, feDisAncestors fe == ctx]) | ctx <- sortedContexts]

-- Render a case group with header
renderCaseGroup :: SymbolTable -> IntMap.IntMap DisjMeta -> (Set.Set (DisjId, Int), [FactEntry]) -> [String]
renderCaseGroup symTbl metaMap (ctx, facts) =
  let header = if Set.null ctx
                 then ["═══ Hypotheses ═══", ""]
                 else ["═══ Case: " ++ renderCaseContext metaMap ctx ++ " ═══", ""]
      body = concatMap (renderFactClean symTbl metaMap) facts
   in header ++ body

-- Render case context as a string
renderCaseContext :: IntMap.IntMap DisjMeta -> Set.Set (DisjId, Int) -> String
renderCaseContext metaMap ctx =
  intercalate ", " [renderCase metaMap (d, i) | (d, i) <- Set.toList ctx]

-- Render a single fact with clean formatting
renderFactClean :: SymbolTable -> IntMap.IntMap DisjMeta -> FactEntry -> [String]
renderFactClean tbl _metaMap fe =
  let isFalse = factName (feFact fe) == PFalse
      factStr = if isFalse
                  then "⊥ (contradiction)"
                  else ppFactWithSymbols tbl (feFact fe)
      labelStr = "F" ++ show (unFactId (feLabel fe))
      thmStr = case feConcThm fe of
                 Just tn -> "by " ++ prettyTheoremName tn
                 Nothing -> "hypothesis"
      deps = feDependencies fe
      depStr = if null deps
                 then ""
                 else " from " ++ unwords (map labelText deps)
      prefix = if isFalse then "  ✓ " else "  "
   in [prefix ++ labelStr ++ " : " ++ factStr
      ,prefix ++ "    " ++ thmStr ++ depStr
      ,""]

-- Render proof summary
renderSummary :: IntMap.IntMap DisjMeta -> [FactEntry] -> [String]
renderSummary metaMap contradictions =
  let -- Group contradictions by case context
      grouped = groupByContext contradictions
      numBranches = length grouped
   in if null contradictions
        then ["", "No contradictions found."]
        else ["", "═══ Proof Summary ═══", ""
             ,"Proved contradiction in " ++ show numBranches ++ " branch" ++ (if numBranches == 1 then "" else "es") ++ ":"
             ,""] ++
             [summarizeBranch metaMap ctx fe
             | (ctx, fes) <- grouped
             , fe <- take 1 fes]

-- | Group facts by their case context, returning list of (context, facts) pairs
groupByContext :: [FactEntry] -> [(Set.Set (DisjId, Int), [FactEntry])]
groupByContext = foldr insertByCtx []
  where
    insertByCtx fe [] = [(feDisAncestors fe, [fe])]
    insertByCtx fe ((ctx, fes):rest)
      | feDisAncestors fe == ctx = (ctx, fe:fes) : rest
      | otherwise = (ctx, fes) : insertByCtx fe rest

-- Summarize a single branch
summarizeBranch :: IntMap.IntMap DisjMeta -> Set.Set (DisjId, Int) -> FactEntry -> String
summarizeBranch metaMap ctx fe =
  let ctxStr = if Set.null ctx
                 then "base case"
                 else renderCaseContext metaMap ctx
      thmStr = case feConcThm fe of
                 Just tn -> prettyTheoremName tn
                 Nothing -> "hypothesis"
   in "  ✓ " ++ ctxStr ++ " → " ++ thmStr

-- Render a case context element nicely
renderCase :: IntMap.IntMap DisjMeta -> (DisjId, Int) -> String
renderCase metaMap (DisjId d, idx) =
  case IntMap.lookup d metaMap of
    Just meta ->
      let val = safeIndex (dmBranchValues meta) idx (show idx)
       in dmVarName meta ++ "=" ++ val
    Nothing -> "D" ++ show d ++ "." ++ show idx

-- Safe list indexing with default value
safeIndex :: [a] -> Int -> a -> a
safeIndex xs i def
  | i < 0 = def
  | otherwise = go xs i
  where
    go [] _ = def
    go (x:_) 0 = x
    go (_:rest) n = go rest (n - 1)

labelText :: Label -> String
labelText (LFact (FactId n)) = "F" ++ show n
labelText (LDisj (DisjId n)) = "D" ++ show n

-- Pretty-print theorem names
prettyTheoremName :: TheoremName -> String
prettyTheoremName tn = case theoremNameText tn of
  "sylow" -> "Sylow's theorem"
  "single_sylow_normal" -> "unique Sylow subgroup is normal"
  "not_simple" -> "simple ∧ not_simple → ⊥"
  "counting_contradiction" -> "element counting"
  "alternating_order" -> "order of alternating group"
  "alternating_simple" -> "Aₙ is simple (n≥5)"
  "lagrange" -> "Lagrange's theorem"
  "divides_contradiction" -> "divisibility contradiction"
  "embed_An" -> "embedding into Aₙ"
  "coset_action" -> "coset action"
  "simple_group_action" -> "simple group action"
  "count_order_pk_elements" -> "counting p^k-order elements"
  "subgroup_index" -> "subgroup index"
  other -> other
