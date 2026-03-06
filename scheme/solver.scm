;;; solver.scm - Forward chaining proof search
;;;
;;; This module implements the main solver loop using agenda-based
;;; forward chaining with trigger indexing.

;;; ============================================================
;;; PROOF ENVIRONMENT
;;; ============================================================

(define-record-type <env>
  (%make-env facts fact-index disjunctions disj-meta disj-key-index
             goal goal-combos closed-branches
             fact-counter disj-counter symbol-counter
             trigger-index iterations)
  env?
  (facts env-facts env-facts-set!)
  (fact-index env-fact-index)
  (disjunctions env-disjunctions env-disjunctions-set!)
  (disj-meta env-disj-meta)
  (disj-key-index env-disj-key-index)
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
              (make-hash-table equal?)         ; disj-key-index
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
;;; ANCESTOR UTILITIES
;;; ============================================================

(define (ancestors-equal? a1 a2)
  "Check if two ancestor hash tables have the same entries.
   Uses size check first for fast rejection, then iterates entries."
  (and (= (hash-table-size a1) (hash-table-size a2))
       (let loop ((entries (hash-table->alist a1)))
         (if (null? entries)
             #t
             (let* ((k (caar entries))
                    (v (cdar entries)))
               (if (equal? (hash-table-ref/default a2 k 'none) v)
                   (loop (cdr entries))
                   #f))))))

(define (ht-subset? small big)
  "Check if every entry in small hash table exists in big with same value."
  (let loop ((entries (hash-table->alist small)))
    (if (null? entries)
        #t
        (let* ((k (caar entries))
               (v (cdar entries)))
          (if (equal? (hash-table-ref/default big k 'none) v)
              (loop (cdr entries))
              #f)))))

(define (branch-is-closed? env ancestors)
  "Check if fact belongs to a branch that already has a contradiction."
  (let loop ((closed (env-closed-branches env)))
    (if (null? closed)
        #f
        (if (ht-subset? (car closed) ancestors)
            #t
            (loop (cdr closed))))))

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
  ;; Skip facts in closed branches (unless it's a contradiction itself)
  (if (and new?
           (not (eq? (fact-predicate fact) 'false))
           (branch-is-closed? env (fact-dis-ancestors fact)))
      #f  ; Branch already closed
      (begin
        ;; Assign label if needed
        (unless (fact-label fact)
          (fact-label-set! fact (env-new-fact-label! env)))

        ;; Check for duplicates
        (let* ((key (fact-key fact))
               (existing (hash-table-ref/default (env-fact-index env) key '())))
          (if (any (lambda (f) (and (fact-equal? f fact)
                                     (ancestors-equal? (fact-dis-ancestors f)
                                                        (fact-dis-ancestors fact))))
                   existing)
              #f  ; Duplicate
              (begin
                ;; Add to facts list
                (env-facts-set! env (cons fact (env-facts env)))

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

                #t))))))  ; New fact added

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
  (let* ((key (disjunction-key disj parent-ancestors theorem-name))
         (existing (hash-table-ref/default (env-disj-key-index env) key #f)))
    (if existing
        '()
        (let ((label (env-new-disj-label! env)))
          (disj-label-set! disj label)
          (hash-table-set! (env-disj-key-index env) key label)

          ;; Store metadata
          (hash-table-set! (env-disj-meta env) label
                           (infer-disj-meta (disj-facts disj)))

          ;; Add to disjunctions list
          (env-disjunctions-set! env (cons disj (env-disjunctions env)))

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
                      (loop (cdr branch-facts) (+ branch-idx 1) new-facts)))))))))

(define (disjunction-key disj parent-ancestors theorem-name)
  "Build a canonical key for disjunction deduplication."
  (let* ((facts-key
          (sort (map pp-fact (disj-facts disj)) string<?))
         (anc-key
          (sort (map (lambda (entry)
                       (let ((k (car entry)))
                         (string-append (car k) "." (number->string (cdr k)))))
                     (hash-table->alist parent-ancestors))
                string<?))
         (thm-key (if theorem-name (symbol->string theorem-name) "")))
    (list facts-key anc-key thm-key)))

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
           (let ((matches
                  (match-premises-with-facts
                   (append before after) env init-subst)))
             (for-each
              (lambda (match-pair)
                (let* ((subst (car match-pair))
                       (remaining-facts (cdr match-pair))
                       (matched (insert-trigger-fact remaining-facts fact trig-idx)))
                  (when (compatible-ancestors? matched)
                    (let ((results (apply-theorem env thm matched subst)))
                      (set! new-facts
                            (fold-left (lambda (acc f) (cons f acc))
                                       new-facts
                                       results))))))
              matches)))))
     triggers)

    new-facts))

(define max-match-results 500)

(define (match-premises-with-facts premises env subst)
  "Match premises and return ((subst . matched-facts) ...)."
  (if (null? premises)
      (list (cons subst '()))
      (let* ((template (car premises))
             (key (fact-key template))
             (candidates (env-lookup env key)))
        (let loop-candidates ((rest candidates)
                              (acc '())
                              (count 0))
          (cond
            ((or (null? rest) (>= count max-match-results))
             acc)
            (else
             (let* ((candidate (car rest))
                    (new-subst (unify-fact template candidate subst)))
               (if new-subst
                   (let loop-results
                       ((results (match-premises-with-facts (cdr premises) env new-subst))
                        (acc2 acc)
                        (count2 count))
                     (cond
                       ((or (null? results) (>= count2 max-match-results))
                        (loop-candidates (cdr rest) acc2 count2))
                       (else
                        (let ((result (car results)))
                          (loop-results
                           (cdr results)
                           (cons (cons (car result) (cons candidate (cdr result)))
                                 acc2)
                           (+ count2 1))))))
                   (loop-candidates (cdr rest) acc count)))))))))

(define (insert-trigger-fact remaining-facts trigger-fact trig-idx)
  "Insert trigger fact at trigger index into remaining matched facts."
  (let loop ((i 0) (rest remaining-facts) (acc '()))
    (cond
      ((= i trig-idx)
       (append (reverse acc) (cons trigger-fact rest)))
      ((null? rest)
       (append (reverse acc) (list trigger-fact)))
      (else
       (loop (+ i 1) (cdr rest) (cons (car rest) acc))))))

;;; ============================================================
;;; MAIN SOLVER LOOP
;;; ============================================================

(define (solve env max-iterations)
  "Run the forward chaining solver."
  (let loop ((front (env-facts env))
             (back '())
             (iter 0))
    (cond
      ;; Goal achieved in all branches
      ((goal-achieved? env)
       (list 'proven iter))

      ;; Exhausted all facts
      ((and (null? front) (null? back))
       (list 'exhausted iter))

      ;; Iteration limit
      ((>= iter max-iterations)
       (list 'limit iter))

      ;; Process next fact
      (else
       (if (null? front)
           (loop (reverse back) '() iter)
           (let ((current (car front)))
             ;; Skip facts in closed branches
             (if (branch-is-closed? env (fact-dis-ancestors current))
                 (loop (cdr front) back iter)
                 (begin
                   (env-iterations-set! env (+ iter 1))
                   (let* ((new-facts (fire-triggered-theorems env current))
                          (next-back (fold-left (lambda (acc f) (cons f acc)) back new-facts)))
                     (loop (cdr front) next-back (+ iter 1)))))))))))

;;; ============================================================
;;; GOAL CHECKING
;;; ============================================================

(define (goal-achieved? env)
  "Check if the goal is proven in all disjunction branches."
  (let ((disjs (env-disjunctions env))
        (proven (append (env-goal-combos env) (env-closed-branches env))))
    (cond
      ;; No disjunctions: just check if goal or contradiction found.
      ((null? disjs)
       (not (null? proven)))
      ;; Avoid deep recursion/combinatorial explosion on large branch forests.
      ((> (length disjs) 16)
       #f)
      ;; With manageable disjunction count: check branch coverage with a cap.
      (else
       (all-branches-covered? disjs proven 50000)))))

(define (all-branches-covered? disjunctions proven-contexts max-combos)
  "Check if all branch combinations are covered by proven contexts.
Returns #f if coverage checking itself exceeds max-combos."
  (let ((choices
         (map (lambda (d)
                (let ((label (disj-label d))
                      (n (length (disj-facts d))))
                  (map (lambda (i) (cons label i)) (iota n))))
              disjunctions))
        (checked 0))
    (letrec ((search
              (lambda (remaining combo)
                (cond
                  ((> checked max-combos) #f)
                  ((null? remaining)
                   (set! checked (+ checked 1))
                   (any (lambda (proven)
                          (context-covers? proven combo))
                        proven-contexts))
                  (else
                   (every (lambda (choice)
                            (search (cdr remaining) (cons choice combo)))
                          (car remaining)))))))
      (search choices '()))))

(define (context-covers? ctx combo)
  "Check if a proven context covers a branch combination."
  ;; ctx is a hash-table, combo is a list of (label . idx) pairs
  ;; ctx covers combo if all entries in ctx are in combo
  (let ((ctx-alist (hash-table->alist ctx)))
    (every (lambda (pair)
             (member pair combo))
           (map car ctx-alist))))

;;; ============================================================
;;; SOLVER ENTRY POINT
;;; ============================================================

(define (auto-solve initial-facts goal theorems max-iterations)
  "Main entry point: set up environment and run solver."
  (let* ((env (make-env initial-facts goal theorems))
         (result (solve env max-iterations)))
    (values env result)))

;;; Utility functions are defined in core.scm
