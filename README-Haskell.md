# Sylow Solver - Haskell Port

A lightweight theorem-proving engine for group theory, specifically designed to solve problems related to Sylow subgroups. This is a Haskell port of the original Python implementation.

## Overview

The Sylow Solver is a specialized theorem prover that can automatically prove or disprove statements about finite groups, particularly focusing on:

- **Sylow theorems** and their applications
- **Group simplicity** questions  
- **Subgroup structure** analysis
- **Order-theoretic** arguments in group theory

## Architecture

The Haskell port maintains the modular structure of the original Python implementation:

### Core Modules

- **`NumberTheory`** - Number-theoretic utilities (primes, divisors, factorization)
- **`Core`** - Fundamental data structures (Facts, Theorems, Disjunctions)  
- **`Environment`** - Proof environment and state management
- **`Auto`** - Automated proof search and theorem application

### Key Features

- **Type-safe** fact and theorem representation
- **Efficient** number-theoretic computations
- **Modular** theorem library with built-in group theory knowledge
- **Automated** proof search with backtracking
- **Extensible** architecture for adding new theorems

## Quick Start

### Building

```bash
cabal configure
cabal build
```

### Running

```bash
cabal run sylow-solver
```

### Testing

```bash
cabal test
```

## Example Usage

```haskell
import Core
import Environment
import Auto
import qualified Data.Map as Map

-- Prove that a group of order 60 is not simple
main = do
  let facts = [group "G", order "G" "60"]
      goal = notSimple "G"
      theorems = [lagrange, simpleNotSimple, sylowTheorem, ...]
      theoremDict = Map.fromList [(theoremName thm, thm) | thm <- theorems]
      env = createProofEnvironment facts theorems theoremDict goal
  
  success <- autoSolve env 20
  if success 
    then putStrLn "Proof found!"
    else putStrLn "Proof search failed"
```

## Number Theory Utilities

The `NumberTheory` module provides efficient implementations of:

```haskell
-- Prime testing and generation
isPrime :: Int -> Bool
primes :: Int -> [Int]

-- Divisor computation  
divisors :: Int -> [Int]
maxPDivisor :: Int -> Int -> Int

-- Prime factorization
primeFactors :: Int -> [Int]  
primeFactorization :: Int -> [(Int, Int)]

-- Sylow-specific utilities
numSylow :: Int -> Int -> [Int]
sylowKillable :: Int -> Bool
```

## Theorem System

### Built-in Theorems

- **Sylow's theorems** - Existence and counting of Sylow subgroups
- **Lagrange's theorem** - Subgroup order divides group order  
- **Alternating group properties** - Order and simplicity
- **Embedding theorems** - Group actions and subgroup embeddings

### Adding Custom Theorems

```haskell
-- Standard theorem with pattern matching
myTheorem :: Theorem  
myTheorem = createTheorem inputPattern conclusions "my_theorem"

-- HyperTheorem with computational rule
myHyperTheorem :: HyperTheorem
myHyperTheorem = createHyperTheorem inputPattern ruleFunction "my_hyper_theorem"
  where
    ruleFunction facts = -- custom logic here
```

## Comparison with Python Version

### Advantages of the Haskell Port

- **Type Safety** - Compile-time guarantees prevent many runtime errors
- **Performance** - Lazy evaluation and optimized data structures  
- **Correctness** - Pure functions and immutable data reduce bugs
- **Conciseness** - Pattern matching and higher-order functions

### Maintained Compatibility

- **Same algorithm** - Identical proof search strategy
- **Same theorems** - All mathematical content preserved
- **Same API** - Similar function names and usage patterns
- **Same examples** - All test cases from Python version work

## Project Structure

```
sylow-solver/
├── NumberTheory.hs    # Number theory utilities
├── Core.hs           # Data structures  
├── Environment.hs    # Proof environment
├── Auto.hs          # Theorem proving engine
├── app/
│   └── Main.hs      # Executable demo
├── test/
│   ├── Spec.hs                # Test suite entry
│   ├── NumberTheorySpec.hs    # Number theory tests
│   ├── CoreSpec.hs           # Core data structure tests
│   └── AutoSpec.hs          # Theorem proving tests
└── sylow-solver.cabal        # Package configuration
```

## Testing

The test suite includes:

- **Unit tests** for all number theory functions
- **Property tests** using QuickCheck  
- **Integration tests** for theorem application
- **Compatibility tests** against Python reference implementation

Run tests with:
```bash
cabal test --test-show-details=direct
```

## Contributing

To extend the theorem prover:

1. **Add theorems** to the `Auto` module
2. **Add number theory utilities** to `NumberTheory` if needed
3. **Write tests** in the appropriate `test/*Spec.hs` file
4. **Update documentation** in this README

## License

MIT License - see original Python implementation for details.

## References

- Original Python implementation by Daniel Menezes
- Sylow theorems and finite group theory
- Automated theorem proving techniques