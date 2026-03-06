;;; main.scm - Entry point and examples for the Sylow solver
;;;
;;; This module provides the main interface for running the solver
;;; and includes example proofs.

;;; ============================================================
;;; LOAD ALL MODULES
;;; ============================================================

;;; In MIT Scheme, load these files in order:
;;; (load "core.scm")
;;; (load "unification.scm")
;;; (load "theorems.scm")
;;; (load "solver.scm")
;;; (load "proof-tree.scm")
;;; (load "main.scm")

;;; ============================================================
;;; CONVENIENCE FUNCTIONS
;;; ============================================================

(define default-max-iterations 1500)

(define (prove-not-simple group-order . maybe-max-iterations)
  "Prove that a simple group of the given order leads to contradiction.
Optional second argument sets max iterations."
  (let ((max-iterations
         (if (null? maybe-max-iterations)
             default-max-iterations
             (car maybe-max-iterations))))
  (let* ((g (sym 'G))
         (n (num group-order))
         (goal (make-fact 'not_simple (list g)))
         (initial-facts
          (list (hypothesis 'group (list g))
                (hypothesis 'order (list g n))
                (hypothesis 'simple (list g)))))
    (call-with-values
        (lambda () (auto-solve initial-facts goal all-theorems max-iterations))
      (lambda (env result)
        (display-result env result group-order)
        (values env result))))))

(define (display-verbose-proof env)
  "Display the full proof with derivation chains like the Haskell version."
  (let* ((facts (env-facts env))
         (meta-map (env-disj-meta env))
         (grouped (group-facts-by-context facts meta-map)))

    ;; Display each case group
    (for-each
     (lambda (group)
       (display-case-header (car group) meta-map)
       (display-facts-in-group (cdr group) env)
       (newline))
     grouped)

    ;; Display proof summary
    (display-proof-summary env meta-map)))

(define (group-facts-by-context facts meta-map)
  "Group facts by their case context, returning ((context . facts) ...)."
  (let ((groups (make-hash-table equal?)))
    ;; Group facts by context
    (for-each
     (lambda (f)
       (let* ((ctx (fact-dis-ancestors f))
              (ctx-key (context->key ctx))
              (existing (hash-table-ref/default groups ctx-key '())))
         (hash-table-set! groups ctx-key (cons f existing))))
     facts)
    ;; Convert to list and sort by context depth (hypotheses first)
    (let ((entries (hash-table->alist groups)))
      (map (lambda (entry)
             (cons (car entry) (reverse (cdr entry))))
           (sort entries
                 (lambda (a b)
                   (< (length (car a)) (length (car b)))))))))

(define (context->key ctx)
  "Convert a context hash-table to a sorted list for use as a key."
  (sort (hash-table->alist ctx)
        (lambda (a b)
          (string<? (format-context-entry a)
                    (format-context-entry b)))))

(define (format-context-entry entry)
  "Format a context entry for sorting."
  (string-append (caar entry) "." (number->string (cdar entry))))

(define (display-case-header ctx-key meta-map)
  "Display a case header like ═══ Case: n₂=1 ═══"
  (if (null? ctx-key)
      (begin
        (display "═══ Hypotheses ═══")
        (newline))
      (begin
        (display "═══ Case: ")
        (display (format-context-key ctx-key meta-map))
        (display " ═══")
        (newline)))
  (newline))

(define (format-context-key ctx-key meta-map)
  "Format a context key as a readable string like 'n₂=1, n₃=10'."
  (string-join
   (map (lambda (entry)
          (let* ((disj-id (caar entry))
                 (idx (cdar entry))
                 (meta (hash-table-ref/default meta-map disj-id #f)))
            (if meta
                (string-append (disj-meta-var-name meta) "="
                               (safe-list-ref (disj-meta-branch-values meta) idx "?"))
                (string-append disj-id "." (number->string idx)))))
        ctx-key)
   ", "))

(define (display-facts-in-group facts env)
  "Display facts in a group with their derivations."
  ;; Sort facts: conclusions (false, not_simple) last
  (let ((sorted (sort-facts-for-display facts)))
    (for-each
     (lambda (f)
       (display-single-fact f env))
     sorted)))

(define (sort-facts-for-display facts)
  "Sort facts so conclusions appear last."
  (let ((conclusions '())
        (others '()))
    (for-each
     (lambda (f)
       (if (or (eq? (fact-predicate f) 'false)
               (eq? (fact-predicate f) 'not_simple))
           (set! conclusions (cons f conclusions))
           (set! others (cons f others))))
     facts)
    (append (reverse others) (reverse conclusions))))

(define (display-single-fact f env)
  "Display a single fact with its derivation."
  (let* ((pred (fact-predicate f))
         (is-conclusion (or (eq? pred 'false) (eq? pred 'not_simple)))
         (label (or (fact-label f) "?"))
         (thm (fact-theorem f))
         (deps (fact-deps f)))

    ;; Fact line with optional checkmark for conclusions
    (if is-conclusion
        (display "  ✓ ")
        (display "  "))
    (display label)
    (display " : ")
    (if (eq? pred 'false)
        (display "⊥ (contradiction)")
        (display (pp-fact f)))
    (newline)

    ;; Derivation line
    (if is-conclusion
        (display "  ✓     by ")
        (display "      by "))
    (display (pretty-theorem-name thm))
    (when (pair? deps)
      (display " from ")
      (display (string-join deps " ")))
    (newline)
    (newline)))

;;; pretty-theorem-name is defined in proof-tree.scm (loaded before main.scm)

(define (display-proof-summary env meta-map)
  "Display the proof summary at the end."
  (let* ((goals (env-goal-combos env))
         (closed (env-closed-branches env))
         (total-branches (+ (length goals) (length closed))))

    (display "═══ Proof Summary ═══")
    (newline)
    (newline)

    (if (and (null? goals) (null? closed))
        (display "No proof found.")
        (begin
          (display (string-append "Proved "
                                  (if (pair? goals) "goal" "contradiction")
                                  " in "
                                  (number->string total-branches)
                                  " branch"
                                  (if (= total-branches 1) "" "es")
                                  ":"))
          (newline)
          (newline)

          ;; Show each successful branch
          (for-each
           (lambda (ctx)
             (display "  ✓ ")
             (display (format-branch-result ctx meta-map env))
             (newline))
           (append goals closed))))
    (newline)))

(define (format-branch-result ctx meta-map env)
  "Format a branch result for the summary."
  (let ((ctx-str (if (zero? (hash-table-size ctx))
                     "base case"
                     (format-context-key (context->key ctx) meta-map))))
    ;; Find how this branch was resolved
    (let ((conclusion (find-branch-conclusion ctx env)))
      (string-append ctx-str " → " conclusion))))

(define (find-branch-conclusion ctx env)
  "Find how a branch was concluded."
  (let ((facts (env-facts env)))
    ;; Look for not_simple or false in this context
    (let loop ((fs facts))
      (if (null? fs)
          "resolved"
          (let* ((f (car fs))
                 (f-ctx (fact-dis-ancestors f))
                 (pred (fact-predicate f)))
            (if (and (context-matches? f-ctx ctx)
                     (or (eq? pred 'false) (eq? pred 'not_simple)))
                (cond
                  ((eq? pred 'false)
                   (case (fact-theorem f)
                     ((not_simple_contradiction) "simple ∧ not_simple → ⊥")
                     ((counting_contradiction) "element counting")
                     ((divides_contradiction) "divisibility contradiction")
                     (else "contradiction")))
                  ((eq? pred 'not_simple)
                   (case (fact-theorem f)
                     ((single_sylow_normal) "unique Sylow → normal → not simple")
                     (else "not simple")))
                  (else "resolved"))
                (loop (cdr fs))))))))

(define (context-matches? f-ctx target-ctx)
  "Check if fact context matches target context."
  ;; Uses ancestors-equal? from solver.scm
  (ancestors-equal? f-ctx target-ctx))

(define (display-result env result order)
  "Display the solver result."
  (newline)
  (display "═══════════════════════════════════════════════")
  (newline)
  (display (string-append "Analyzing group of order " (number->string order)))
  (newline)
  (display "═══════════════════════════════════════════════")
  (newline)
  (newline)

  (case (car result)
    ((proven)
     (display "✓ PROVEN: Group is not simple")
     (newline)
     (display (string-append "  Iterations: " (number->string (cadr result))))
     (newline)
     (display (string-append "  Facts derived: " (number->string (length (env-facts env)))))
     (newline)
     (display (string-append "  Disjunctions: " (number->string (length (env-disjunctions env)))))
     (newline)
     (newline)
     ;; Show full proof with derivation chains
     (display-verbose-proof env))

    ((exhausted)
     (display "✗ EXHAUSTED: Could not prove (group may be simple)")
     (newline)
     (display (string-append "  Iterations: " (number->string (cadr result))))
     (newline))

    ((limit)
     (display "⚠ LIMIT: Iteration limit reached")
     (newline)
     (display (string-append "  Iterations: " (number->string (cadr result))))
     (newline)))

  (newline))

;;; ============================================================
;;; EXAMPLES
;;; ============================================================

(define (example-order-60)
  "Prove that a group of order 60 with the simple assumption leads to specific Sylow counts."
  (display "Example: Group of order 60 = 2² × 3 × 5")
  (newline)
  (display "This is the order of A₅, the smallest non-abelian simple group.")
  (newline)
  (display "The solver uses a bounded search (100 iterations) and should report EXHAUSTED/LIMIT, not PROVEN.")
  (newline)
  (prove-not-simple 60 100))

(define (example-order-30)
  "Prove a group of order 30 is not simple."
  (display "Example: Group of order 30 = 2 × 3 × 5")
  (newline)
  (display "Expected: Single Sylow subgroup forces not simple.")
  (newline)
  (prove-not-simple 30))

(define (example-order-56)
  "Prove a group of order 56 is not simple."
  (display "Example: Group of order 56 = 2³ × 7")
  (newline)
  (prove-not-simple 56))

(define (example-order-36)
  "Prove a group of order 36 is not simple."
  (display "Example: Group of order 36 = 2² × 3²")
  (newline)
  (prove-not-simple 36))

(define (example-order-100)
  "Prove a group of order 100 is not simple."
  (display "Example: Group of order 100 = 2² × 5²")
  (newline)
  (prove-not-simple 100))

(define (example-order-168)
  "Analyze a group of order 168 = 2³ × 3 × 7 (order of PSL(2,7))."
  (display "Example: Group of order 168 = 2³ × 3 × 7")
  (newline)
  (display "This is the order of PSL(2,7), a simple group.")
  (newline)
  (display "The solver should exhaust possibilities without finding a contradiction.")
  (newline)
  (prove-not-simple 168))

;;; ============================================================
;;; BATCH TESTING
;;; ============================================================

(define (test-range start end)
  "Test all orders from start to end."
  (let loop ((n start) (simple-candidates '()))
    (if (> n end)
        (begin
          (newline)
          (display "═══════════════════════════════════════════════")
          (newline)
          (display "SUMMARY")
          (newline)
          (display "═══════════════════════════════════════════════")
          (newline)
          (display (string-append "Tested orders " (number->string start)
                                  " to " (number->string end)))
          (newline)
          (display "Potential simple group orders (could not prove not-simple):")
          (newline)
          (for-each (lambda (n) (display (string-append "  " (number->string n))) (newline))
                    (reverse simple-candidates))
          (newline))
        (begin
          (call-with-values
              (lambda () (prove-not-simple n))
            (lambda (env result)
              (if (eq? (car result) 'proven)
                  (loop (+ n 1) simple-candidates)
                  (loop (+ n 1) (cons n simple-candidates)))))))))

;;; ============================================================
;;; INTERACTIVE HELP
;;; ============================================================

(define (help)
  "Display help information."
  (display "
Sylow Solver - MIT Scheme Implementation
=========================================

BASIC COMMANDS:

  (prove-not-simple n)      - Prove group of order n is not simple
  (example-order-60)        - Run example for order 60 (A₅)
  (example-order-30)        - Run example for order 30
  (example-order-168)       - Run example for order 168 (PSL(2,7))
  (test-range s e)          - Test all orders from s to e
  (help)                    - Show this help

AMB-BASED SOLVER (uses call/cc for backtracking):

  (prove-not-simple-amb n)  - Same as above, using amb for matching
  (amb-collect body ...)    - Collect all solutions from amb choices
  (with-amb body ...)       - Run with amb, return #f if no solution
  (with-amb-all body ...)   - Collect all amb solutions

AMB PRIMITIVES:

  (amb x y z ...)           - Non-deterministically choose one value
  (amb-list lst)            - Choose one element from list
  (require condition)       - Backtrack if condition is false
  (fail)                    - Explicitly backtrack

EXAMPLE - Pythagorean triples:

  (amb-example-pythagorean 20)
  => ((3 4 5) (5 12 13) (6 8 10) (8 15 17) (9 12 15) (12 16 20))

The solver uses forward chaining with Sylow's theorems to prove
that groups of certain orders cannot be simple. The amb variant
demonstrates idiomatic Scheme style using continuations.

Example usage:
  > (prove-not-simple 60)
  > (prove-not-simple-amb 30)
  > (test-range 2 100)
")
  (newline))

;;; ============================================================
;;; RUN MAIN EXAMPLE
;;; ============================================================

(define (main)
  "Main entry point."
  (help)
  (example-order-30))

;;; Uncomment to run automatically when loaded:
;;; (main)
