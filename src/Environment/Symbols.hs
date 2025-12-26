{-# LANGUAGE RecordWildCards #-}

module Environment.Symbols
  ( SymbolTable
  , generateNewSymbol
  , nextSymbol
  , internSymbol
  , symbolTable
  , lookupSymbolName
  , registerSymbol
  ) where

import Core
import Environment.Types
import qualified Data.Map.Strict as Map
import qualified Data.IntMap.Strict as IntMap

type SymbolTable = IntMap.IntMap String

-- | Core symbol generation logic (pure).
-- Given current letter, suffix, and map of used symbols,
-- returns (newSymbol, nextLetter, nextSuffix).
nextSymbol :: Char -> Int -> Map.Map String a -> (String, Char, Int)
nextSymbol curLetter curSuffix usedSymbols =
  let suffix = if curSuffix == 0 then "" else show curSuffix
      symTxt = curLetter : suffix
      nextLetter' = if curLetter == 'Z' then 'A' else succ curLetter
      nextSuffix' = if curLetter == 'Z' then curSuffix + 1 else curSuffix
   in if Map.member symTxt usedSymbols
        then nextSymbol nextLetter' nextSuffix' usedSymbols
        else (symTxt, nextLetter', nextSuffix')

-- | Register a symbol in the generator state.
-- Updates symbol table, symbol names, and increments the next ID.
{-# INLINE registerSymbol #-}
registerSymbol :: Symbol -> GeneratorState -> GeneratorState
registerSymbol symVal gs@GeneratorState{..} =
  let name = symbolName symVal
      sid = unSymbolId (symbolId symVal)
  in gs
    { gsSymbolTable = Map.insert name symVal gsSymbolTable
    , gsSymbolNames = IntMap.insert sid name gsSymbolNames
    , gsNextSymbolId = SymbolId (sid + 1)
    }

-- | Generate a new unique symbol in the environment.
generateNewSymbol :: ProofEnvironment -> (Symbol, ProofEnvironment)
generateNewSymbol env =
  let (symTxt, nextLetter, nextSuffix) =
        nextSymbol (peCurLetter env) (peCurSuffix env) (peSymbolTable env)
      symId = peNextSymbolId env
      symVal = Symbol symId symTxt
      env' = updateGenState
               (\gs -> (registerSymbol symVal gs)
                   { gsCurLetter = nextLetter
                   , gsCurSuffix = nextSuffix
                   })
               env
   in (symVal, env')

-- | Pure helper to intern or create a symbol given its name.
-- If symbol exists, return it without any state updates (optimization).
-- If new, batch all updates in a single updateGenState call.
internSymbol :: String -> ProofEnvironment -> (Symbol, ProofEnvironment)
internSymbol s env =
  case Map.lookup s (peSymbolTable env) of
    Just symFound -> (symFound, env)  -- Already registered, no updates needed
    Nothing ->
      let symId = peNextSymbolId env
          symNew = Symbol symId s
          env' = updateGenState
                   (\gs -> (registerSymbol symNew gs)
                        { gsStats = (gsStats gs) { esSymbols = esSymbols (gsStats gs) + 1 }
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
