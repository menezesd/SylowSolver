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

(define (prove-not-simple group-order)
  "Prove that a simple group of the given order leads to contradiction."
  (let* ((g (sym 'G))
         (n (num group-order))
         (goal (make-fact 'not_simple (list g)))
         (initial-facts
          (list (hypothesis 'group (list g))
                (hypothesis 'order (list g n))
                (hypothesis 'simple (list g)))))
    (call-with-values
        (lambda () (auto-solve initial-facts goal all-theorems 10000))
      (lambda (env result)
        (display-result env result group-order)
        (values env result)))))

(define (display-simple-summary env)
  "Display a detailed summary of how the proof succeeded."
  (display "Proof Summary:")
  (newline)
  (display "══════════════")
  (newline)
  (newline)

  ;; Show goal achievements
  (let ((goals (env-goal-combos env))
        (closed (env-closed-branches env))
        (meta-map (env-disj-meta env)))
    (display (string-append "  Goal achieved in "
                            (number->string (length goals))
                            " branch(es)"))
    (newline)
    (display (string-append "  Contradictions in "
                            (number->string (length closed))
                            " branch(es)"))
    (newline)
    (newline)

    ;; Show key derived information
    (display "Prime Factorization & Sylow Analysis:")
    (newline)
    (display "─────────────────────────────────────")
    (newline)
    (display-sylow-info env)
    (newline)

    ;; Show disjunction splits
    (display "Case Analysis:")
    (newline)
    (display "──────────────")
    (newline)
    (display-case-splits env meta-map)
    (newline)

    ;; Show conclusions in each branch
    (display "Conclusions by Branch:")
    (newline)
    (display "──────────────────────")
    (newline)
    (display-branch-conclusions env meta-map goals closed)))

(define (display-sylow-info env)
  "Display Sylow subgroup information derived in the proof."
  (let* ((facts (env-facts env))
         (sylow-counts (filter (lambda (f)
                                 (eq? (fact-predicate f) 'num_sylow))
                               facts)))
    (when (pair? sylow-counts)
      (display "  Sylow subgroup count constraints (by Sylow's theorem):")
      (newline)
      (let ((by-prime (group-sylow-by-prime sylow-counts)))
        (for-each
         (lambda (entry)
           (display "    n")
           (display (subscript-string (car entry)))
           (display " ≡ 1 (mod ")
           (display (car entry))
           (display "), n")
           (display (subscript-string (car entry)))
           (display " | |G| → n")
           (display (subscript-string (car entry)))
           (display " ∈ {")
           (display (string-join (map number->string (cdr entry)) ", "))
           (display "}")
           (newline))
         by-prime)))))

(define (group-sylow-by-prime sylow-facts)
  "Group num_sylow facts by prime, returning ((prime . values) ...)."
  (let ((ht (make-hash-table equal?)))
    (for-each
     (lambda (f)
       (let* ((args (fact-args f))
              (p (arg-value (car args)))
              (n (arg-value (caddr args)))
              (existing (hash-table-ref/default ht p '())))
         (unless (member n existing)
           (hash-table-set! ht p (cons n existing)))))
     sylow-facts)
    (map (lambda (p)
           (cons (number->string p)
                 (sort (hash-table-ref ht p) <)))
         (sort (hash-table-keys ht) <))))

(define (hash-table-keys ht)
  "Get all keys from a hash table."
  (let ((keys '()))
    (hash-table-walk ht (lambda (k v) (set! keys (cons k keys))))
    keys))

(define (display-case-splits env meta-map)
  "Display the case splits used in the proof (deduplicated)."
  (let ((disjs (env-disjunctions env))
        (seen (make-hash-table equal?)))
    (let loop ((ds disjs) (i 0))
      (unless (null? ds)
        (let* ((d (car ds))
               (label (disj-label d))
               (meta (hash-table-ref/default meta-map label
                                             (make-disj-meta "case" '())))
               (var-name (disj-meta-var-name meta))
               (values (disj-meta-branch-values meta))
               (key (cons var-name values)))
          (unless (hash-table-ref/default seen key #f)
            (hash-table-set! seen key #t)
            (display "  • Case split: ")
            (display var-name)
            (display " ∈ {")
            (display (string-join values ", "))
            (display "}")
            (newline))
          (loop (cdr ds) (+ i 1)))))))

(define (display-branch-conclusions env meta-map goals closed)
  "Display how each branch was resolved."
  ;; Group not_simple facts by their disjunction ancestors
  (let* ((facts (env-facts env))
         (goal-facts (filter (lambda (f)
                               (eq? (fact-predicate f) 'not_simple))
                             facts))
         (shown-reasons (make-hash-table equal?)))

    ;; Collect unique reasons for not_simple
    (for-each
     (lambda (f)
       (let* ((ctx (fact-dis-ancestors f))
              (thm (fact-theorem f))
              (reason (get-concise-reason f env)))
         (when reason
           (let ((key reason))
             (unless (hash-table-ref/default shown-reasons key #f)
               (hash-table-set! shown-reasons key thm))))))
     goal-facts)

    ;; Display goal achievements
    (hash-table-walk
     shown-reasons
     (lambda (reason thm)
       (display "  ✓ ")
       (display reason)
       (newline)))

    ;; Collect and display unique contradictions
    (let ((shown-contras (make-hash-table equal?)))
      (for-each
       (lambda (ctx)
         (let ((ctx-str (if (zero? (hash-table-size ctx))
                            "Base case"
                            (render-context ctx meta-map))))
           (unless (hash-table-ref/default shown-contras ctx-str #f)
             (hash-table-set! shown-contras ctx-str #t)
             (display "  ✗ ")
             (display ctx-str)
             (display ": element counting contradiction")
             (newline))))
       closed))))

(define (get-concise-reason f env)
  "Get a concise reason string for why goal was achieved."
  (let ((thm (fact-theorem f))
        (deps (fact-deps f))
        (facts (env-facts env)))
    (cond
      ((eq? thm 'single_sylow_normal)
       ;; Find the num_sylow(p, G, 1) fact this came from
       (let loop ((ds deps))
         (if (null? ds)
             #f
             (let ((dep (find (lambda (fact)
                                (equal? (fact-label fact) (car ds)))
                              facts)))
               (if (and dep
                        (eq? (fact-predicate dep) 'num_sylow)
                        (= (length (fact-args dep)) 3)
                        (eqv? (arg-value (caddr (fact-args dep))) 1))
                   (string-append "n"
                                  (subscript-string (arg-display (car (fact-args dep))))
                                  " = 1 → unique Sylow subgroup is normal → not simple")
                   (loop (cdr ds)))))))
      ((eq? thm 'counting_contradiction)
       "Element counting yields contradiction")
      (else #f))))

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
     ;; Show simple summary instead of full tree (tree has performance issues)
     (display-simple-summary env))

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
  (display "The proof explores Sylow subgroup counts.")
  (newline)
  (prove-not-simple 60))

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
