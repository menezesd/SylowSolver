;;; amb.scm - Non-deterministic choice with backtracking
;;;
;;; This module implements McCarthy's amb operator using call/cc.
;;; It provides a clean, declarative way to express search problems.
;;;
;;; The key insight: amb captures the continuation at each choice point,
;;; allowing us to backtrack and try alternatives when we hit a dead end.

;;; ============================================================
;;; FAILURE CONTINUATION
;;; ============================================================

;;; The failure continuation - called when we need to backtrack.
;;; Initially set to signal an error (no more alternatives).

(define *fail*
  (lambda ()
    (error "amb: no more alternatives")))

;;; ============================================================
;;; CORE AMB OPERATOR
;;; ============================================================

(define (amb . alternatives)
  "Choose one of the alternatives. Backtracks on failure."
  (if (null? alternatives)
      (*fail*)  ; No alternatives - backtrack
      (call/cc
       (lambda (continuation)
         ;; Save the current failure continuation
         (let ((previous-fail *fail*))
           ;; Set up new failure: try next alternative
           (set! *fail*
                 (lambda ()
                   (set! *fail* previous-fail)  ; Restore old failure
                   (continuation (apply amb (cdr alternatives)))))
           ;; Return first alternative
           (car alternatives))))))

(define (amb-list lst)
  "Choose one element from a list."
  (apply amb lst))

(define (require condition)
  "Fail (backtrack) if condition is false."
  (unless condition (*fail*)))

(define (fail)
  "Explicitly trigger backtracking."
  (*fail*))

;;; ============================================================
;;; COLLECTING ALL SOLUTIONS
;;; ============================================================

;;; For the theorem prover, we often want ALL solutions, not just the first.
;;; This macro runs a body and collects all values it can produce via amb.

(define-syntax amb-collect
  (syntax-rules ()
    ((_ body ...)
     (amb-collect-impl (lambda () body ...)))))

(define (amb-collect-impl thunk)
  "Collect all solutions from a thunk using amb."
  (let ((solutions '())
        (outer-fail *fail*))
    (call/cc
     (lambda (escape)
       ;; Set up failure to collect and continue
       (set! *fail*
             (lambda ()
               (set! *fail* outer-fail)  ; Restore outer failure
               (escape (reverse solutions))))
       ;; Run the thunk
       (let ((result (thunk)))
         ;; Got a result - save it and backtrack for more
         (set! solutions (cons result solutions))
         (*fail*))))))

;;; Alternative: amb-find-all using a simpler continuation approach
(define (amb-find-all thunk)
  "Find all solutions by running thunk repeatedly with backtracking."
  (let ((results '()))
    (call/cc
     (lambda (done)
       (let ((saved-fail *fail*))
         (set! *fail*
               (lambda ()
                 (set! *fail* saved-fail)
                 (done (reverse results))))
         (let loop ()
           (let ((result (thunk)))
             (set! results (cons result results))
             (*fail*))))))))

;;; ============================================================
;;; UTILITIES
;;; ============================================================

(define (amb-reset!)
  "Reset the failure continuation (use between independent searches)."
  (set! *fail* (lambda () (error "amb: no more alternatives"))))

;;; with-amb: Run body in a fresh amb context, returning #f if no solution.
(define-syntax with-amb
  (syntax-rules ()
    ((_ body ...)
     (call/cc
      (lambda (escape)
        (let ((saved-fail *fail*))
          (set! *fail*
                (lambda ()
                  (set! *fail* saved-fail)
                  (escape #f)))
          (let ((result (begin body ...)))
            (set! *fail* saved-fail)
            result)))))))

;;; with-amb-all: Run body collecting all solutions via amb.
(define-syntax with-amb-all
  (syntax-rules ()
    ((_ body ...)
     (amb-find-all (lambda () body ...)))))

;;; ============================================================
;;; EXAMPLES AND TESTS
;;; ============================================================

(define (amb-example-pythagorean limit)
  "Find Pythagorean triples up to limit."
  (with-amb-all
   (let* ((a (amb-list (iota-from 1 limit)))
          (b (amb-list (iota-from a limit)))
          (c (amb-list (iota-from b limit))))
     (require (= (+ (* a a) (* b b)) (* c c)))
     (list a b c))))

(define (iota-from start end)
  "Generate list (start start+1 ... end)."
  (if (> start end)
      '()
      (cons start (iota-from (+ start 1) end))))

;;; ============================================================
;;; AMB-BASED PREMISE MATCHING
;;; ============================================================

;;; This is the key integration with the theorem prover.
;;; We express premise matching as a series of amb choices.

(define (match-premises-amb premises env initial-subst)
  "Match premises against facts using amb for backtracking.
   Returns a list of all valid substitutions."
  (with-amb-all
   (match-premises-amb-inner premises env initial-subst)))

(define (match-premises-amb-inner premises env subst)
  "Inner recursive matching - uses amb to choose candidates."
  (if (null? premises)
      subst  ; Success - return the substitution
      (let* ((template (car premises))
             (key (fact-key template))
             (candidates (env-lookup env key)))
        ;; Fail if no candidates
        (require (pair? candidates))
        ;; Choose a candidate (amb will backtrack through all)
        (let* ((candidate (amb-list candidates))
               (new-subst (unify-fact template candidate subst)))
          ;; Require successful unification
          (require new-subst)
          ;; Continue with remaining premises
          (match-premises-amb-inner (cdr premises) env new-subst)))))

;;; Version that also tracks which facts were matched
(define (match-with-facts-amb premises env initial-subst)
  "Match premises, returning (subst . matched-facts) pairs."
  (with-amb-all
   (match-with-facts-inner premises env initial-subst '())))

(define (match-with-facts-inner premises env subst matched)
  "Match premises, accumulating matched facts."
  (if (null? premises)
      (cons subst (reverse matched))
      (let* ((template (car premises))
             (candidates (env-lookup env (fact-key template))))
        (require (pair? candidates))
        (let* ((candidate (amb-list candidates))
               (new-subst (unify-fact template candidate subst)))
          (require new-subst)
          ;; Check compatibility with previously matched facts
          (require (compatible-with-all? candidate matched))
          (match-with-facts-inner (cdr premises) env new-subst
                                  (cons candidate matched))))))

(define (compatible-with-all? fact facts)
  "Check if fact is compatible with all facts in the list."
  (every (lambda (f) (compatible-pair? fact f)) facts))

(define (compatible-pair? f1 f2)
  "Check if two facts have compatible disjunction ancestors."
  (let ((a1 (fact-dis-ancestors f1))
        (a2 (fact-dis-ancestors f2)))
    (call/cc
     (lambda (return)
       (hash-table-walk
        a1
        (lambda (key val)
          (let ((other (hash-table-ref/default a2 (car key) 'none)))
            (when (and (not (eq? other 'none))
                       (not (= other (cdr key))))
              (return #f)))))
       #t))))

;;; ============================================================
;;; INCREMENTAL MATCHING WITH AMB
;;; ============================================================

(define (fire-theorem-amb env thm trigger-fact trigger-idx)
  "Fire a theorem with amb-based matching for remaining premises."
  (let* ((premises (thm-premises thm))
         (trigger-prem (list-ref premises trigger-idx))
         (before (take premises trigger-idx))
         (after (drop premises (+ trigger-idx 1)))
         (remaining (append before after))
         (init-subst (unify-fact trigger-prem trigger-fact (make-substitution))))
    (if (not init-subst)
        '()  ; Trigger didn't match
        ;; Use amb to find all ways to match remaining premises
        (with-amb-all
         (let ((subst (match-premises-amb-inner remaining env init-subst)))
           ;; Reconstruct matched facts for the result
           (cons subst (cons trigger-fact
                             (map (lambda (prem)
                                    (find-matching-fact prem env subst))
                                  remaining))))))))

(define (find-matching-fact template env subst)
  "Find the fact that matches template under subst."
  (let ((candidates (env-lookup env (fact-key template))))
    (find (lambda (f) (unify-fact template f subst)) candidates)))
