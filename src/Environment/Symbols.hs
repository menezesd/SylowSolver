module Environment.Symbols
  ( generateNewSymbol
  ) where

import Environment.Types
import Environment.Accessors
import Data.Set (Set)
import qualified Data.Set as Set

-- Generate a new unique symbol (like A, B, C, ..., Z, A1, B1, etc.)
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
                ( updateGenState (\gs -> gs
                    { gsCurLetter = nextLetter
                    , gsCurSuffix = nextSuffix
                    , gsSymbolSet = Set.insert sym (gsSymbolSet gs)
                    }) env
                , sym
                )
   in go (peCurLetter env) (peCurSuffix env)
