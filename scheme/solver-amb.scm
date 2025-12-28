;;; solver-amb.scm - Forward chaining solver using amb for backtracking
;;;
;;; This is an alternative solver implementation that uses the amb
;;; operator for premise matching, demonstrating idiomatic Scheme style.

;;; ============================================================
;;; AMB-BASED THEOREM FIRING
;;; ============================================================

(define (fire-triggered-theorems-amb env fact)
  "Find and fire all theorems triggered by a new fact, using amb."
  (let* ((key (fact-key fact))
         (triggers (hash-table-ref/default (env-trigger-index env) key '())))
    (append-map
     (lambda (trigger)
       (fire-single-theorem-amb env trigger fact))
     triggers)))

(define (fire-single-theorem-amb env trigger trigger-fact)
  "Fire a single theorem with amb-based matching."
  (let* ((thm (trigger-theorem trigger))
         (trig-idx (trigger-premise-index trigger))
         (premises (thm-premises thm))
         (trig-prem (list-ref premises trig-idx))
         (init-subst (unify-fact trig-prem trigger-fact (make-substitution))))

    (if (not init-subst)
        '()  ; Trigger premise didn't match
        (let* ((before (take premises trig-idx))
               (after (drop premises (+ trig-idx 1)))
               (remaining (append before after))
               ;; Use amb to find all valid completions
               (completions (match-with-trigger-amb
                             remaining trigger-fact env init-subst)))
          ;; Apply theorem for each valid completion
          (append-map
           (lambda (completion)
             (let ((subst (car completion))
                   (matched-facts (cdr completion)))
               (apply-theorem env thm matched-facts subst)))
           completions)))))

(define (match-with-trigger-amb remaining trigger-fact env init-subst)
  "Match remaining premises, including trigger-fact in compatibility check."
  (with-amb-all
   (let ((result (match-remaining-amb remaining trigger-fact env init-subst '())))
     result)))

(define (match-remaining-amb premises trigger-fact env subst matched)
  "Recursively match premises using amb for choice."
  (if (null? premises)
      ;; All premises matched - return (subst . all-matched-facts)
      (cons subst (cons trigger-fact (reverse matched)))

      (let* ((template (car premises))
             (candidates (env-lookup env (fact-key template))))
        ;; Fail if no candidates
        (require (pair? candidates))

        ;; Non-deterministically choose a candidate
        (let* ((candidate (amb-list candidates))
               (new-subst (unify-fact template candidate subst)))
          ;; Require successful unification
          (require new-subst)

          ;; Require compatibility with trigger and previous matches
          (require (compatible-with-fact? candidate trigger-fact))
          (require (all-compatible? candidate matched))

          ;; Continue with remaining premises
          (match-remaining-amb (cdr premises) trigger-fact env new-subst
                               (cons candidate matched))))))

(define (compatible-with-fact? f1 f2)
  "Check if two facts have compatible disjunction branches."
  (let ((a1 (fact-dis-ancestors f1))
        (a2 (fact-dis-ancestors f2)))
    (call/cc
     (lambda (return)
       ;; Check each entry in a1 against a2
       (hash-table-walk
        a1
        (lambda (key _)
          (let* ((disj-label (car key))
                 (branch-idx (cdr key))
                 ;; Look for same disjunction in a2
                 (found #f))
            (hash-table-walk
             a2
             (lambda (key2 _)
               (when (equal? (car key2) disj-label)
                 (set! found #t)
                 (unless (= (cdr key2) branch-idx)
                   (return #f)))))))) ; Different branches - incompatible
       #t))))

(define (all-compatible? fact facts)
  "Check if fact is compatible with all facts in list."
  (or (null? facts)
      (and (compatible-with-fact? fact (car facts))
           (all-compatible? fact (cdr facts)))))

;;; ============================================================
;;; SOLVER USING AMB
;;; ============================================================

(define (solve-amb env max-iterations)
  "Run the solver using amb-based matching."
  (amb-reset!)  ; Start with fresh amb state
  (let loop ((agenda (env-facts env))
             (iter 0))
    (cond
      ;; Goal achieved in all branches
      ((goal-achieved? env)
       (list 'proven iter))

      ;; Exhausted all facts
      ((null? agenda)
       (list 'exhausted iter))

      ;; Iteration limit
      ((>= iter max-iterations)
       (list 'limit iter))

      ;; Process next fact
      (else
       (env-iterations-set! env (+ iter 1))
       (let ((new-facts (fire-triggered-theorems-amb env (car agenda))))
         (loop (append (cdr agenda) new-facts) (+ iter 1)))))))

(define (auto-solve-amb initial-facts goal theorems max-iterations)
  "Main entry point using amb-based solver."
  (let* ((env (make-env initial-facts goal theorems))
         (result (solve-amb env max-iterations)))
    (values env result)))

;;; ============================================================
;;; EXPLORATORY SEARCH WITH AMB
;;; ============================================================

;;; This variant uses amb more extensively - it non-deterministically
;;; explores the search space, backtracking when stuck.

(define (solve-exploratory env goal max-depth)
  "Exploratory solver using full amb-based search."
  (with-amb
   (explore-from env (env-facts env) goal 0 max-depth)))

(define (explore-from env facts goal depth max-depth)
  "Explore from current state, using amb for choices."
  (cond
    ;; Goal found
    ((any (lambda (f) (fact-matches-goal? f goal)) (env-facts env))
     'proven)

    ;; Contradiction in all branches - we're done with this path
    ((goal-achieved? env)
     'proven)

    ;; Depth limit
    ((>= depth max-depth)
     (fail))  ; Backtrack

    ;; No more facts to process
    ((null? facts)
     (fail))  ; Backtrack

    ;; Choose which fact to process (amb explores all orderings)
    (else
     (let* ((fact (amb-list facts))
            (remaining (remove-first fact facts))
            (new-facts (fire-triggered-theorems-amb env fact)))
       (explore-from env
                     (append remaining new-facts)
                     goal
                     (+ depth 1)
                     max-depth)))))

(define (remove-first item lst)
  "Remove first occurrence of item from list."
  (cond
    ((null? lst) '())
    ((equal? (car lst) item) (cdr lst))
    (else (cons (car lst) (remove-first item (cdr lst))))))

;;; ============================================================
;;; PROOF SEARCH WITH CONTINUATION-BASED DISJUNCTIONS
;;; ============================================================

;;; This is an alternative architecture where disjunctions actually
;;; fork the computation using continuations.

(define (solve-forking initial-facts goal theorems)
  "Solver that forks at disjunctions using continuations."
  (let ((all-branches-succeed #t))
    (call/cc
     (lambda (done)
       (let ((branch-fail
              (lambda ()
                (set! all-branches-succeed #f)
                (done 'failed))))

         (define (process-conclusions conclusions env)
           (for-each
            (lambda (conc)
              (case (conclusion-type conc)
                ((fact)
                 (let ((f (conclusion-content conc)))
                   (env-add-fact! env f #t)
                   (when (fact-matches-goal? f goal)
                     (done 'proven))
                   (when (eq? (fact-predicate f) 'false)
                     (branch-fail))))
                ((disjunction)
                 ;; Fork! Try each branch
                 (let ((branches (disj-facts (conclusion-content conc))))
                   (fork-branches branches env goal)))))
            conclusions))

         (define (fork-branches branches env goal)
           (if (null? branches)
               (branch-fail)  ; No branches succeeded
               (call/cc
                (lambda (try-next)
                  (let ((branch-env (copy-env env)))
                    ;; Try this branch
                    (env-add-fact! branch-env (car branches) #t)
                    ;; Continue search in this branch
                    ;; (simplified - would need full search here)
                    (try-next 'continue))
                  ;; Try remaining branches
                  (fork-branches (cdr branches) env goal)))))

         ;; Main search would go here
         'exhausted)))))

;;; ============================================================
;;; CONVENIENCE WRAPPER
;;; ============================================================

(define (prove-not-simple-amb group-order)
  "Prove group is not simple using amb-based solver."
  (let* ((g (sym 'G))
         (n (num group-order))
         (goal (make-fact 'not_simple (list g)))
         (initial-facts
          (list (hypothesis 'group (list g))
                (hypothesis 'order (list g n))
                (hypothesis 'simple (list g)))))
    (call-with-values
        (lambda () (auto-solve-amb initial-facts goal all-theorems 10000))
      (lambda (env result)
        (display-result env result group-order)
        (values env result)))))
