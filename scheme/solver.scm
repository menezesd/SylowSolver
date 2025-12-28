;;; solver.scm - Forward chaining proof search
;;;
;;; This module implements the main solver loop using agenda-based
;;; forward chaining with trigger indexing.

;;; ============================================================
;;; PROOF ENVIRONMENT
;;; ============================================================

(define-record-type <env>
  (%make-env facts fact-index disjunctions disj-meta
             goal goal-combos closed-branches
             fact-counter disj-counter symbol-counter
             trigger-index iterations)
  env?
  (facts env-facts env-facts-set!)
  (fact-index env-fact-index)
  (disjunctions env-disjunctions env-disjunctions-set!)
  (disj-meta env-disj-meta)
  (goal env-goal)
  (goal-combos env-goal-combos env-goal-combos-set!)
  (closed-branches env-closed-branches env-closed-branches-set!)
  (fact-counter env-fact-counter env-fact-counter-set!)
  (disj-counter env-disj-counter env-disj-counter-set!)
  (symbol-counter env-symbol-counter env-symbol-counter-set!)
  (trigger-index env-trigger-index)
  (iterations env-iterations env-iterations-set!))

(define (make-env initial-facts goal theorems)
  "Create a new proof environment."
  (let ((env (%make-env
              '()                              ; facts
              (make-hash-table equal?)         ; fact-index
              '()                              ; disjunctions
              (make-hash-table equal?)         ; disj-meta
              goal                             ; goal
              '()                              ; goal-combos
              '()                              ; closed-branches
              0                                ; fact-counter
              0                                ; disj-counter
              0                                ; symbol-counter
              (build-trigger-index theorems)   ; trigger-index
              0)))                             ; iterations
    ;; Add initial facts
    (for-each (lambda (f) (env-add-fact! env f #f)) initial-facts)
    env))

;;; ============================================================
;;; LABEL GENERATION
;;; ============================================================

(define (env-new-fact-label! env)
  (let ((n (env-fact-counter env)))
    (env-fact-counter-set! env (+ n 1))
    (string-append "F" (number->string n))))

(define (env-new-disj-label! env)
  (let ((n (env-disj-counter env)))
    (env-disj-counter-set! env (+ n 1))
    (string-append "D" (number->string n))))

(define (env-fresh-symbol! env prefix)
  "Generate a fresh symbol for theorem conclusions."
  (let ((n (env-symbol-counter env)))
    (env-symbol-counter-set! env (+ n 1))
    (sym (string->symbol (string-append prefix (number->string n))))))

;;; ============================================================
;;; FACT MANAGEMENT
;;; ============================================================

(define (env-add-fact! env fact new?)
  "Add a fact to the environment. Returns #t if it's new."
  ;; Assign label if needed
  (unless (fact-label fact)
    (fact-label-set! fact (env-new-fact-label! env)))

  ;; Check for duplicates
  (let* ((key (fact-key fact))
         (existing (hash-table-ref/default (env-fact-index env) key '())))
    (if (any (lambda (f) (and (fact-equal? f fact)
                               (equal? (hash-table->alist (fact-dis-ancestors f))
                                       (hash-table->alist (fact-dis-ancestors fact)))))
             existing)
        #f  ; Duplicate
        (begin
          ;; Add to facts list
          (env-facts-set! env (append (env-facts env) (list fact)))

          ;; Add to index
          (hash-table-set! (env-fact-index env) key (cons fact existing))

          ;; Check for contradiction
          (when (eq? (fact-predicate fact) 'false)
            (env-closed-branches-set!
             env (cons (hash-table-copy (fact-dis-ancestors fact))
                       (env-closed-branches env))))

          ;; Check for goal
          (when (fact-matches-goal? fact (env-goal env))
            (env-goal-combos-set!
             env (cons (hash-table-copy (fact-dis-ancestors fact))
                       (env-goal-combos env))))

          #t))))  ; New fact added

(define (env-lookup env key)
  "Look up facts by (predicate . arity) key."
  (hash-table-ref/default (env-fact-index env) key '()))

(define (fact-matches-goal? fact goal)
  "Check if a fact matches the goal."
  (and (eq? (fact-predicate fact) (fact-predicate goal))
       (= (length (fact-args fact)) (length (fact-args goal)))
       (every (lambda (fa ga)
                (or (variable? ga)
                    (arg-equal? fa ga)))
              (fact-args fact)
              (fact-args goal))))

;;; ============================================================
;;; DISJUNCTION MANAGEMENT
;;; ============================================================

(define (env-add-disjunction! env disj theorem-name deps parent-ancestors)
  "Add a disjunction, creating branch facts."
  (let ((label (env-new-disj-label! env)))
    (disj-label-set! disj label)

    ;; Store metadata
    (hash-table-set! (env-disj-meta env) label
                     (infer-disj-meta (disj-facts disj)))

    ;; Add to disjunctions list
    (env-disjunctions-set! env (append (env-disjunctions env) (list disj)))

    ;; Create branch facts
    (let loop ((branch-facts (disj-facts disj))
               (branch-idx 0)
               (new-facts '()))
      (if (null? branch-facts)
          new-facts
          (let* ((bf (car branch-facts))
                 (new-ancestors (hash-table-copy parent-ancestors)))
            ;; Add this branch to ancestry
            (hash-table-set! new-ancestors (cons label branch-idx) #t)

            ;; Set up the branch fact
            (fact-deps-set! bf (list label))
            (fact-dis-ancestors-set! bf new-ancestors)
            (fact-theorem-set! bf theorem-name)

            ;; Add to environment
            (if (env-add-fact! env bf #t)
                (loop (cdr branch-facts) (+ branch-idx 1) (cons bf new-facts))
                (loop (cdr branch-facts) (+ branch-idx 1) new-facts)))))))

;;; ============================================================
;;; THEOREM APPLICATION
;;; ============================================================

(define (apply-theorem env thm matched-facts subst)
  "Apply a theorem with the given substitution, returning new facts."
  ;; Check compatibility of input facts
  (if (not (compatible-ancestors? matched-facts))
      '()
      (let ((parent-ancestors (merge-ancestors matched-facts))
            (dep-labels (filter-map fact-label matched-facts))
            (thm-name (thm-name thm))
            (new-facts '()))

        (let ((conclusions
               (if (theorem? thm)
                   ;; Standard theorem: apply substitution to conclusion templates
                   (map (lambda (templ)
                          (conc-fact (apply-subst-fact subst templ env)))
                        (theorem-conclusions thm))
                   ;; Hyper-theorem: call the rule function
                   ((hyper-theorem-rule thm) matched-facts subst env))))

          ;; Process each conclusion
          (for-each
           (lambda (conc)
             (case (conclusion-type conc)
               ((fact)
                (let ((f (conclusion-content conc)))
                  (fact-deps-set! f dep-labels)
                  (fact-dis-ancestors-set! f (hash-table-copy parent-ancestors))
                  (fact-theorem-set! f thm-name)
                  (when (env-add-fact! env f #t)
                    (set! new-facts (cons f new-facts)))))
               ((disjunction)
                (let ((branch-facts
                       (env-add-disjunction! env (conclusion-content conc)
                                             thm-name dep-labels parent-ancestors)))
                  (set! new-facts (append branch-facts new-facts))))))
           conclusions)

          new-facts))))

;;; ============================================================
;;; INCREMENTAL MATCHING
;;; ============================================================

(define (fire-triggered-theorems env fact)
  "Find and fire all theorems triggered by a new fact."
  (let* ((key (fact-key fact))
         (triggers (hash-table-ref/default (env-trigger-index env) key '()))
         (new-facts '()))

    (for-each
     (lambda (trigger)
       (let* ((thm (trigger-theorem trigger))
              (trig-idx (trigger-premise-index trigger))
              (premises (thm-premises thm))
              (trig-prem (list-ref premises trig-idx))
              (before (take premises trig-idx))
              (after (drop premises (+ trig-idx 1)))
              (init-subst (unify-fact trig-prem fact (make-substitution))))

         (when init-subst
           ;; Find all ways to match remaining premises
           (let ((substs (match-remaining-premises before after env init-subst)))
             (for-each
              (lambda (subst)
                ;; Reconstruct matched facts for compatibility check
                (let ((matched (reconstruct-matched-facts
                                premises fact trig-idx env subst)))
                  (when matched
                    (let ((results (apply-theorem env thm matched subst)))
                      (set! new-facts (append results new-facts))))))
              substs)))))
     triggers)

    new-facts))

(define (reconstruct-matched-facts premises trigger-fact trig-idx env subst)
  "Reconstruct the list of matched facts from substitution."
  (let loop ((i 0) (prems premises) (matched '()))
    (cond
      ((null? prems)
       (and (compatible-ancestors? (reverse matched))
            (reverse matched)))
      ((= i trig-idx)
       (loop (+ i 1) (cdr prems) (cons trigger-fact matched)))
      (else
       (let* ((prem (car prems))
              (key (fact-key prem))
              (candidates (env-lookup env key))
              (match (find (lambda (f) (unify-fact prem f subst)) candidates)))
         (if match
             (loop (+ i 1) (cdr prems) (cons match matched))
             #f))))))

;;; ============================================================
;;; MAIN SOLVER LOOP
;;; ============================================================

(define (solve env max-iterations)
  "Run the forward chaining solver."
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
       (let ((new-facts (fire-triggered-theorems env (car agenda))))
         (loop (append (cdr agenda) new-facts) (+ iter 1)))))))

;;; ============================================================
;;; GOAL CHECKING
;;; ============================================================

(define (goal-achieved? env)
  "Check if the goal is proven in all disjunction branches."
  (let ((disjs (env-disjunctions env))
        (proven (append (env-goal-combos env) (env-closed-branches env))))
    (if (null? disjs)
        ;; No disjunctions: just check if goal or contradiction found
        (not (null? proven))
        ;; With disjunctions: all branch combinations must be covered
        (all-branches-covered? disjs proven))))

(define (all-branches-covered? disjunctions proven-contexts)
  "Check if all branch combinations are covered by proven contexts."
  (let* ((branch-choices
          (map (lambda (d)
                 (let ((label (disj-label d))
                       (n (length (disj-facts d))))
                   (map (lambda (i) (cons label i))
                        (iota n))))
               disjunctions))
         (all-combos (cartesian-product branch-choices)))
    (every (lambda (combo)
             (any (lambda (proven)
                    (context-covers? proven combo))
                  proven-contexts))
           all-combos)))

(define (context-covers? ctx combo)
  "Check if a proven context covers a branch combination."
  ;; ctx is a hash-table, combo is a list of (label . idx) pairs
  ;; ctx covers combo if all entries in ctx are in combo
  (let ((ctx-alist (hash-table->alist ctx)))
    (every (lambda (pair)
             (member pair combo))
           (map car ctx-alist))))

(define (cartesian-product lists)
  "Generate all combinations from lists of choices."
  (if (null? lists)
      '(())
      (let ((rest (cartesian-product (cdr lists))))
        (append-map (lambda (x)
                      (map (lambda (r) (cons x r)) rest))
                    (car lists)))))

;;; ============================================================
;;; SOLVER ENTRY POINT
;;; ============================================================

(define (auto-solve initial-facts goal theorems max-iterations)
  "Main entry point: set up environment and run solver."
  (let* ((env (make-env initial-facts goal theorems))
         (result (solve env max-iterations)))
    (values env result)))

;;; Utility functions are defined in core.scm
