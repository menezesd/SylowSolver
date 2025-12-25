module Environment.Symbols
  ( SymbolTable
  , generateNewSymbol
  , nextSymbol
  , internSymbol
  , symbolTable
  , lookupSymbolName
  ) where

import Core
import Environment.Types
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap
import qualified Data.Set as Set

type SymbolTable = IntMap.IntMap String

-- | Core symbol generation logic (pure).
-- Given current letter, suffix, and set of used symbols,
-- returns (newSymbol, nextLetter, nextSuffix).
nextSymbol :: Char -> Int -> Set.Set String -> (String, Char, Int)
nextSymbol curLetter curSuffix usedSymbols =
  let suffix = if curSuffix == 0 then "" else show curSuffix
      symTxt = curLetter : suffix
      nextLetter = if curLetter == 'Z' then 'A' else succ curLetter
      nextSuffix = if curLetter == 'Z' then curSuffix + 1 else curSuffix
   in if Set.member symTxt usedSymbols
        then nextSymbol nextLetter nextSuffix usedSymbols
        else (symTxt, nextLetter, nextSuffix)

-- | Generate a new unique symbol in the environment.
generateNewSymbol :: ProofEnvironment -> (Symbol, ProofEnvironment)
generateNewSymbol env =
  let (symTxt, nextLetter, nextSuffix) =
        nextSymbol (peCurLetter env) (peCurSuffix env) (peSymbolSet env)
      symVal = Symbol (peNextSymbolId env) symTxt
      env' = updateGenState
               (\gs ->
                 gs
                   { gsCurLetter = nextLetter
                   , gsCurSuffix = nextSuffix
                   , gsSymbolSet = Set.insert symTxt (gsSymbolSet gs)
                   , gsSymbolTable = Map.insert symTxt symVal (gsSymbolTable gs)
                   , gsSymbolNames = IntMap.insert (unSymbol symVal) symTxt (gsSymbolNames gs)
                   , gsNextSymbolId = gsNextSymbolId gs + 1
                   })
               env
   in (symVal, env')

-- | Pure helper to intern or create a symbol given its name.
internSymbol :: String -> ProofEnvironment -> (Symbol, ProofEnvironment)
internSymbol s env =
  case Map.lookup s (peSymbolTable env) of
    Just symFound ->
      let env' = updateGenState
                   (\gs -> gs { gsSymbolSet = Set.insert s (gsSymbolSet gs) })
                   env
       in (symFound, env')
    Nothing ->
      let symNew = Symbol (peNextSymbolId env) s
          env' = updateGenState
                   (\gs ->
                     gs { gsSymbolTable = Map.insert s symNew (gsSymbolTable gs)
                        , gsSymbolSet = Set.insert s (gsSymbolSet gs)
                        , gsSymbolNames = IntMap.insert (unSymbol symNew) s (gsSymbolNames gs)
                        , gsNextSymbolId = gsNextSymbolId gs + 1
                        , gsStats = (gsStats gs) { esSymbols = esSymbols (gsStats gs) + 1 }
                        })
                   env
       in (symNew, env')

-- | Extract the symbol table from the environment.
symbolTable :: ProofEnvironment -> SymbolTable
symbolTable = peSymbolNames

-- | Lookup the printable name for a symbol, falling back to the embedded name.
lookupSymbolName :: SymbolTable -> Symbol -> String
lookupSymbolName tbl symVal =
  IntMap.findWithDefault (symbolName symVal) (unSymbol symVal) tbl
