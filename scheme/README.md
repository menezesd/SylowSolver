# Sylow Solver - MIT Scheme Implementation

An automated theorem prover for group theory, specifically for proving that
groups of certain orders cannot be simple using Sylow's theorems.

## Requirements

- MIT Scheme (tested with 11.2+)
- SRFI-9 (define-record-type) - built into MIT Scheme
- SRFI-69 (hash-tables) - built into MIT Scheme

## Files

| File | Description |
|------|-------------|
| `core.scm` | Core data types: arguments, facts, disjunctions, conclusions |
| `unification.scm` | Unification and substitution for theorem matching |
| `theorems.scm` | Theorem definitions (Sylow, Lagrange, counting, etc.) |
| `solver.scm` | Forward chaining proof search with trigger indexing |
| `amb.scm` | Non-deterministic choice operator using `call/cc` |
| `solver-amb.scm` | Alternative solver using amb for backtracking |
| `proof-tree.scm` | Proof tree building and ASCII rendering |
| `main.scm` | Entry point, examples, and help |

## Usage

### Loading in MIT Scheme

```scheme
(load "core.scm")
(load "unification.scm")
(load "theorems.scm")
(load "solver.scm")
(load "proof-tree.scm")
(load "main.scm")
```

Or use the provided loader:

```bash
mit-scheme --load core.scm --load unification.scm --load theorems.scm \
           --load solver.scm --load proof-tree.scm --load main.scm
```

### Running Examples

```scheme
;; Show help
(help)

;; Prove a group of order 30 is not simple
(prove-not-simple 30)

;; Run the order-60 example (A₅)
(example-order-60)

;; Test a range of orders
(test-range 2 100)
```

### Example Output

```
═══════════════════════════════════════════════
Analyzing group of order 30
═══════════════════════════════════════════════

✓ PROVEN: Group is not simple
  Iterations: 15
  Facts derived: 23
  Disjunctions: 1

Proof Structure:
════════════════════

• F0: group(G) [hypothesis]
• F1: order(G, 30) [hypothesis]
• F2: simple(G) [hypothesis]
• F5: num_sylow(5, G, 1) [sylow]
• F8: not_simple(G) [single_sylow_normal]

═══ Proof Summary ═══

Proved goal in 1 branch:

  ✓ base case
```

## The `amb` Operator

The `amb` module implements McCarthy's non-deterministic choice operator
using `call/cc`. This is a classic Scheme technique for backtracking search.

### How `amb` Works

```scheme
;; amb captures the continuation at each choice point
(define (find-pair-summing-to n lst)
  (with-amb
   (let* ((x (amb-list lst))
          (y (amb-list lst)))
     (require (= (+ x y) n))
     (list x y))))

(find-pair-summing-to 10 '(1 3 5 7 9))
=> (3 7)  ; or (7 3), depending on order

;; Collect ALL solutions
(with-amb-all
 (let* ((x (amb-list '(1 2 3)))
        (y (amb-list '(1 2 3))))
   (require (< x y))
   (list x y)))
=> ((1 2) (1 3) (2 3))
```

### Using `amb` for Premise Matching

The standard solver uses explicit list accumulation:

```scheme
;; Explicit approach
(define (match-premises premises env subst)
  (if (null? premises)
      (list subst)
      (append-map
       (lambda (candidate)
         (let ((new-subst (unify-fact (car premises) candidate subst)))
           (if new-subst
               (match-premises (cdr premises) env new-subst)
               '())))
       (env-lookup env (fact-key (car premises))))))
```

With `amb`, this becomes declarative:

```scheme
;; amb approach - reads like a specification
(define (match-premises-amb premises env subst)
  (with-amb-all
   (if (null? premises)
       subst
       (let* ((candidate (amb-list (env-lookup env (fact-key (car premises)))))
              (new-subst (unify-fact (car premises) candidate subst)))
         (require new-subst)  ; Backtrack if unification fails
         (match-premises-amb (cdr premises) env new-subst)))))
```

The `amb` version is more declarative: we just say "choose a candidate"
and "require it to unify" - the backtracking is handled automatically.

## How It Works

### Forward Chaining Search

1. Start with initial facts (hypotheses)
2. Build a trigger index: map from (predicate, arity) → theorems
3. For each new fact, find triggered theorems via index
4. Match remaining premises against known facts
5. Fire theorem to derive new facts or disjunctions
6. Repeat until goal achieved or exhausted

### Disjunction Handling

When a theorem produces a disjunction (e.g., "n₅ = 1 OR n₅ = 6"), the
solver explores all branches. A proof succeeds only if the goal is
achieved (or a contradiction reached) in ALL branches.

### Key Theorems

- **Sylow's Theorem**: For prime power p^k dividing |G|, there exists
  a Sylow p-subgroup, and n_p ≡ 1 (mod p), n_p | [G:P]

- **Single Sylow → Not Simple**: If n_p = 1, the unique Sylow p-subgroup
  is normal, so G is not simple (unless trivial)

- **Counting Argument**: If the sum of elements in Sylow subgroups
  exceeds |G|, we have a contradiction

- **Lagrange's Theorem**: |H| divides |G| for any subgroup H

## Comparison with Python/Haskell Versions

| Aspect | Scheme | Python | Haskell |
|--------|--------|--------|---------|
| Type safety | Dynamic | Dynamic | Static (GADTs) |
| Records | SRFI-9 | dataclass | data types |
| Hash tables | SRFI-69 | dict | HashMap |
| Pattern matching | Manual dispatch | if/isinstance | Pattern synonyms |
| Performance | Interpreted | Interpreted | Compiled |

## License

Same as the parent project.
