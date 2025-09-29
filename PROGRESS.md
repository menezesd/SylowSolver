Progress and plan for provenance-aware coverage and order-108 parity

Summary
-------
- Implemented JSONL trace emission for Haskell proof steps to `tools/hs_logs.jsonl`.
- Recorded signature-mapped disjunction ancestor combos (sigMap) for both goal- and producer-derived facts.
- Implemented signature-aware coverage matching that enumerates full assignments over referenced disjunctions and checks recorded sigMaps against concrete assignments.
- Iterated provenance policy:
  1. (initial) union-of-goal-and-producer (too permissive; caused false positives)
  2. (hybrid) goal-only when present, else producers (conservative, left uncovered cases)
  3. (refined) allow a producer combo only when its producing FactLabel is in the transitive-dependency closure of at least one recorded goal fact (implemented)
- Added HSpec tests for orders 10, 12, 20, 108 and enabled verbose output for order 108 to capture debug traces.

Current status
--------------
- Tests: focused `order 108 behaves` still fails (Haskell concludes goal not achieved) under the refined provenance rule. Running the specific test produced detailed debug output and JSON summaries with uncovered full assignments.
- The code implementing the refined provenance rule lives in `StateEnvironment.hs` (see `updateGoalAchieved`), and emits per-run JSON summaries with `uncovered_assignments` to `tools/hs_logs.jsonl`.
- The most recent run produced uncovered assignments that combine disjunction labels `D29`, `D3`, `D32`, `D66`, `D8` and show specific concrete signatures (e.g., an assignment with `order(A20,108)` alongside certain `num_sylow` values) that are not covered by recorded goal or allowed producer combos.

Immediate plan
--------------
1. Re-run the focused `order 108 behaves` test (done interactively) and collect the latest `tools/hs_logs.jsonl` lines for analysis.
2. If uncovered assignments remain, inspect recorded producer combos to find candidate producer FactLabels that could legitimately cover them, and verify whether those FactLabels are reachable from goal facts via `factDependencies` (if not, identify why dependencies are missing).
3. If dependencies are missing, audit theorem application sites (where `factDependencies` are constructed) to ensure producers propagate correct dependencies; otherwise, consider relaxing the provenance predicate slightly (for example, allow producer combos if they are reachable via at most one intermediate producer) and validate.
4. When behavior matches Python on order-108, run the full HSpec suite and quiet debug prints.

Next steps (short-term)
-----------------------
- Investigate the uncovered assignments listed in `tools/hs_logs.jsonl` and determine which producer combos could cover them.
- Try a targeted provenance relaxation if dependency propagation is correct but transitive closure is too narrow.

Notes and artifacts
-------------------
- File with JSONL traces: `tools/hs_logs.jsonl`
- Main provenance logic: `StateEnvironment.hs` (function `updateGoalAchieved`)
- Tests: `test/OrderExtraSpec.hs`

Signed-off-by: automated-agent
