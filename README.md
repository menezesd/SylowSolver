# Sylow Solver

Automated reasoning toolkit for Sylow-style group theory proofs, implemented in both Haskell and Python.

## Haskell
- Core solver lives in `src/` with modules for symbols, unification, memoized number theory, matching, and proof rendering.
- Entry point: `app/Main.hs`.
- Build/test: `cabal build`, `cabal test`. Logs land in `dist-newstyle/logs` (see `cabal.project.local`).
- Docs: `readme_haskell.tex` (PDF alongside).

## Python
- Package in `sylow_solver/` with fact/disjunction types, substitution helper, theorem base, proof search, and proof tree rendering.
- CLI: `python3 auto2.py [orders...]` (interactive or batch).
- Tests: `python3 -m pytest tests/test_search.py`.
- Docs: `readme_python.tex` (PDF alongside).

## Quick Start
1. Install GHC/Cabal (for Haskell) and Python 3 with `pytest` (for Python).
2. Run `cabal test` to verify the Haskell build.
3. Run `python3 -m pytest tests/test_search.py` to verify the Python solver.
4. Use `auto2.py` (Python) or `app/Main.hs` (Haskell) to explore proofs for specific group orders.

## Notes
- Haskell substitutions use a `Substitution` newtype; Python uses a small `Substitution` wrapper for matching/unification.
- Symbol rendering goes through symbol tables in both implementations for consistent pretty-printing.
