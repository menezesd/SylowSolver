-- | NumberTheorySpec.hs
--
-- Tests for the NumberTheory module, verifying compatibility with Python implementation.

module NumberTheorySpec where

import Test.Hspec
import Test.QuickCheck
import NumberTheory

spec :: Spec
spec = do
  describe "isPrime" $ do
    it "correctly identifies small primes" $ do
      isPrime 2 `shouldBe` True
      isPrime 3 `shouldBe` True  
      isPrime 5 `shouldBe` True
      isPrime 7 `shouldBe` True
      isPrime 11 `shouldBe` True
      isPrime 13 `shouldBe` True
      
    it "correctly identifies composites" $ do
      isPrime 1 `shouldBe` False
      isPrime 4 `shouldBe` False
      isPrime 6 `shouldBe` False
      isPrime 8 `shouldBe` False
      isPrime 9 `shouldBe` False
      isPrime 10 `shouldBe` False
      
    it "handles edge cases" $ do
      isPrime 0 `shouldBe` False
      isPrime (-1) `shouldBe` False
      
  describe "primes" $ do
    it "generates correct prime list for small inputs" $ do
      primes 10 `shouldBe` [2, 3, 5, 7]
      primes 20 `shouldBe` [2, 3, 5, 7, 11, 13, 17, 19]
      
    it "handles edge cases" $ do
      primes 1 `shouldBe` []
      primes 2 `shouldBe` [2]
      
  describe "divisors" $ do
    it "computes divisors correctly" $ do
      divisors 1 `shouldBe` [1]
      divisors 6 `shouldBe` [1, 2, 3, 6]
      divisors 12 `shouldBe` [1, 2, 3, 4, 6, 12]
      
    it "handles perfect squares" $ do
      divisors 9 `shouldBe` [1, 3, 9]
      divisors 16 `shouldBe` [1, 2, 4, 8, 16]
      
    it "handles edge cases" $ do  
      divisors 0 `shouldBe` []
      divisors (-1) `shouldBe` []
      
  describe "maxPDivisor" $ do
    it "computes maximum p-divisor correctly" $ do
      maxPDivisor 8 2 `shouldBe` 3   -- 2^3 divides 8
      maxPDivisor 12 2 `shouldBe` 2  -- 2^2 divides 12
      maxPDivisor 9 3 `shouldBe` 2   -- 3^2 divides 9
      maxPDivisor 7 2 `shouldBe` 0   -- 2^0 divides 7
      
  describe "primeFactors" $ do
    it "factors numbers correctly" $ do
      primeFactors 12 `shouldBe` [2, 3]
      primeFactors 60 `shouldBe` [2, 3, 5]
      primeFactors 17 `shouldBe` [17]
      
    it "handles edge cases" $ do
      primeFactors 1 `shouldBe` []
      primeFactors 2 `shouldBe` [2]
      
  describe "primeFactorization" $ do
    it "provides factorization with exponents" $ do
      primeFactorization 12 `shouldBe` [(2, 2), (3, 1)]
      primeFactorization 60 `shouldBe` [(2, 2), (3, 1), (5, 1)]
      
  describe "numSylow" $ do
    it "finds Sylow possibilities correctly" $ do
      -- For order 12 = 2^2 * 3, p=2: divisors ≡ 1 (mod 2) are 1, 3
      numSylow 2 12 `shouldBe` [1, 3]
      -- For order 12, p=3: divisors ≡ 1 (mod 3) are 1, 4  
      numSylow 3 12 `shouldBe` [1, 4]
      
  describe "pKillable" $ do
    it "determines p-killability correctly" $ do
      -- Order 6 = 2*3: for p=2, divisors are [1,2,3,6], only 1,3 ≡ 1 (mod 2)
      -- So there exists d>1 (namely 3) with d ≡ 1 (mod 2), so not 2-killable
      pKillable 2 6 `shouldBe` False
      -- For p=3, divisors [1,2,3,6], none except 1 ≡ 1 (mod 3), so 3-killable
      pKillable 3 6 `shouldBe` True
      
  describe "sylowKillable" $ do
    it "determines Sylow killability" $ do
      sylowKillable 1 `shouldBe` True   -- trivial group
      sylowKillable 6 `shouldBe` True   -- 3-killable (from above)
      -- Groups that are not Sylow-killable are more complex to construct
      
  describe "property tests" $ do
    it "prime factors are distinct for the number" $ property $ \n ->
      n > 1 ==> all (\p -> n `mod` p == 0) (primeFactors n)
      
    it "all prime factors are actually prime" $ property $ \n ->
      n > 1 ==> all isPrime (primeFactors n)
      
    it "divisors always include 1 and n (for n > 0)" $ property $ \n ->
      n > 0 ==> let divs = divisors n in 1 `elem` divs && n `elem` divs