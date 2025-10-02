-- | Mathematical utilities for Sylow theorems
module Math where

import Data.List (group, sort)
import Errors

-- Prime factorization and divisors
primesUpTo :: Integer -> [Integer]
primesUpTo n = sieve [2..n]
  where 
    sieve [] = []
    sieve (p:xs) = p : sieve [x | x <- xs, x `mod` p /= 0]

-- | Safe prime factorization with error handling
primeFactorization :: Integer -> ProverResult [(Integer, Int)]
primeFactorization n 
  | n <= 0 = Left $ ParseError $ "Cannot factorize non-positive number: " ++ show n
  | n == 1 = Right []
  | otherwise = Right $ runLengthEncode $ primeFactors n
  where
    primeFactors num = factorize num (primesUpTo (ceiling $ sqrt $ fromIntegral num))
    
    factorize 1 _ = []
    factorize m [] = [m] -- m is prime
    factorize m (p:ps)
      | m `mod` p == 0 = p : factorize (m `div` p) (p:ps)
      | otherwise = factorize m ps

    runLengthEncode [] = []
    runLengthEncode (x:xs) = 
      let (same, rest) = span (== x) xs
      in (x, 1 + length same) : runLengthEncode rest

-- | All divisors of n with error handling
allDivisors :: Integer -> ProverResult [Integer]
allDivisors n = do
  factors <- primeFactorization n
  let divisorCombinations = sequence [[p^e | e <- [0..k]] | (p, k) <- factors]
  return $ map product divisorCombinations

-- | Safe factorial with bounds checking
factorial :: Integer -> ProverResult Integer
factorial m 
  | m < 0 = Left $ ParseError $ "Cannot compute factorial of negative number: " ++ show m
  | m > 20 = Left $ ResourceLimitError $ "Factorial too large: " ++ show m ++ " (limit: 20)"
  | otherwise = Right $ product [1..m]

-- | Highest power of p that divides n
-- | Compute the highest power of p that divides n
highestPowerDividing :: Integer -> Integer -> Integer
highestPowerDividing p n
  | n <= 0 || p <= 1 = 0
  | n `mod` p /= 0 = 0
  | otherwise = 1 + highestPowerDividing p (n `div` p)

-- Unique elements (using more descriptive name)
unique :: Ord a => [a] -> [a]
unique = map head . group . sort
  where
    group [] = []
    group (x:xs) = let (same, rest) = span (== x) xs
                   in (x : same) : group rest