module DisjunctionHash
  ( disjLabelNumber
  ) where

import Data.Hashable (hash)

disjLabelNumber :: String -> Int
disjLabelNumber canon =
  let h = hash canon
      n = abs h `mod` 1000000
   in n
