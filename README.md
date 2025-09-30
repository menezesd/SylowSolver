SylowSolver — tiny Sylow-based theorem prover prototype
===============================================

What this project is
---------------------
SylowSolver is a compact Haskell prototype that explores a proof-search architecture built from:

- a simple fact language (named predicates with string arguments),
- parametric theorem/technique templates that match facts up to renaming, and
- case-splitting via disjunctions (the engine records which alternative an inferred fact depends on).

The project is intentionally small and exploratory: it implements a handful of Sylow-related tactics that can derive contradictions for a few small group orders and prints human-friendly proofs with case-splits and provenance.

Key features
------------

- Facts carry provenance (hypothesis or theorem application).
- Disjunctions are represented explicitly; facts can depend on a particular disjunction alternative.
- The prover produces a structured trace of events (now `TraceEvent`) for each fact or disjunction insertion.
- A pretty-printer reconstructs proofs for chosen case assignments, collapses repeated subtrees by stable numbering, and shows substitutions used during theorem application.

Files of interest
-----------------

- `SylowSolver.hs` — main program (engine, theorems, pretty-printer).
- `README.md`, `readme.tex` — this documentation.

Build & run
-----------

This project uses Cabal and GHC (tested with GHC 9.4.7 in the dev container). From the repository root:

```bash
# build
cabal build

# run with an integer argument (group order)
cabal run sylow-solver -- 40
```

If you run the program without arguments it defaults to a quick demo (orders 40 and 24 are run in sequence when no stdin data is provided).

What the program prints
-----------------------

When the prover finds a contradiction it prints a human-readable proof that includes:

- the case assignment(s) for each disjunction (which alternative was chosen),
- the status of each alternative (chosen / ok / fails for the same assignment),
- a numbered derivation tree with cross-references for repeated subtrees,
- provenance lines showing which theorem produced a fact and the substitution used.

Example (trimmed):

```
Attempting: no simple group of order 40
✓ CONTRADICTION derived (goal proven).
--- Case assignment ---
SylowDivisibilityCongruence(group["G"], order["G","40"]) => chosen alt 0
  *[0] numSylow(2, G, 1) (chosen)
   [1] numSylow(2, G, 5) (ok)
Proof:
[1] false()
  — by UniqueSylowImpliesNotSimple  {G := G, p := 5} (from: simple(G), numSylow(5, G, 1))
  [2] simple(G)
    — hypothesis
  [3] numSylow(5, G, 1)
    — by SylowDivisibilityCongruence  {G := G, n := 40} (from: group(G), order(G, 40))
    [4] group(G)
      — hypothesis
    [5] order(G, 40)
      — hypothesis
```

Structured trace (developer feature)
-------------------------------------

The engine now emits a structured `TraceEvent` stream while it runs. Each event is one of:

- `TraceFactInserted` — a fact inserted (with the theorem name, parent deps, parents list and substitution), or
- `TraceDisjInserted` — a disjunction created by a theorem (with its id, label, alternatives, deps and substitution map).

`runProver` returns this trace in addition to the success flag and final environment. This makes it easier to test, export or post-process proofs programmatically.

Development notes and next steps
-------------------------------

- The code currently lives in a single file (`SylowSolver.hs`). Splitting into modules (`Sylow.Core`, `Sylow.Engine`, `Sylow.Print`) will improve maintainability and testability.
- Replace partial-record selectors where possible to silence warnings and avoid brittle code.
- Add unit tests verifying that small orders yield expected `TraceEvent` sequences.
- Optionally serialize `TraceEvent` to JSON for external tooling.

# Automating Sylow's Theorems

This project is an attempt to automate the process of proving that there are no simple groups of a given order by leveraging Sylow's theorems and related techniques from finite group theory.

## Overview

Nearly every introductory group theory course has a problem set with a series of problems of the form "prove that there are no simple groups of order n," for various values of n. While the specific details vary, nearly all of these problems can be solved by applying a relatively small set of techniques based on Sylow's theorems and some related arguments involving counting, embeddings into alternating groups, and normalizers of intersections of Sylow subgroups.

Since computers are excellent at applying logical rules systematically, it is natural to attempt to automate the process of solving these types of problems. This project represents an initial proof of concept in this direction.

## Implementation

The core idea is to encode various Sylow techniques as "theorem" objects that can be applied to a collection of established facts to derive new facts. For example, one theorem object directly applies Sylow's theorems to list out the possible numbers of Sylow p-subgroups for a given group order. Another theorem handles the counting argument based on the fact that Sylow p-subgroups of prime order must have trivial intersection.

These theorem objects are composed into a simple theorem prover that maintains a collection of established facts and repeatedly applies the theorems to derive new facts. If a contradiction is ever derived (encoded as the "false" fact), then the theorem prover has successfully shown there are no simple groups of the given order.

While the current implementation is fairly basic, combining just a handful of standard Sylow techniques, it demonstrates the potential for further automating arguments in finite group theory by encoding more sophisticated techniques as theorem objects.

## Usage

python3 auto2.py


