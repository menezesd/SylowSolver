module Environment.Symbols
  ( generateNewSymbol
  , nextSymbol
  ) where

import Environment.Types
import qualified Data.Set as Set

-- | Core symbol generation logic (pure).
-- Given current letter, suffix, and set of used symbols,
-- returns (newSymbol, nextLetter, nextSuffix).
nextSymbol :: Char -> Int -> Set.Set String -> (String, Char, Int)
nextSymbol curLetter curSuffix usedSymbols =
  let suffix = if curSuffix == 0 then "" else show curSuffix
      sym = curLetter : suffix
      nextLetter = if curLetter == 'Z' then 'A' else succ curLetter
      nextSuffix = if curLetter == 'Z' then curSuffix + 1 else curSuffix
   in if Set.member sym usedSymbols
        then nextSymbol nextLetter nextSuffix usedSymbols
        else (sym, nextLetter, nextSuffix)

-- | Generate a new unique symbol in the environment.
generateNewSymbol :: ProofEnvironment -> (String, ProofEnvironment)
generateNewSymbol env =
  let (sym, nextLetter, nextSuffix) =
        nextSymbol (peCurLetter env) (peCurSuffix env) (peSymbolSet env)
      env' = updateGenState
               (\gs ->
                 gs
                   { gsCurLetter = nextLetter
                   , gsCurSuffix = nextSuffix
                   , gsSymbolSet = Set.insert sym (gsSymbolSet gs)
                   })
               env
   in (sym, env')
