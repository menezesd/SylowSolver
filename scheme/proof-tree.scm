;;; proof-tree.scm - Proof tree building and rendering
;;;
;;; This module builds a tree structure from the proof trace,
;;; grouping facts by their case context (disjunction branches).

;;; ============================================================
;;; PROOF TREE DATA STRUCTURES
;;; ============================================================

(define-record-type <proof-tree>
  (%make-proof-tree kind fact-info next-tree
                    disj-id var-name branches explanation)
  proof-tree?
  (kind pt-kind)                    ; 'empty | 'fact | 'case-split | 'contradiction
  (fact-info pt-fact-info)          ; <fact-info> or #f
  (next-tree pt-next-tree)          ; <proof-tree> or #f
  (disj-id pt-disj-id)              ; string or #f
  (var-name pt-var-name)            ; string or #f
  (branches pt-branches)            ; list of <case-branch>
  (explanation pt-explanation))     ; string or #f

(define-record-type <case-branch>
  (make-case-branch disj-id branch-idx label children)
  case-branch?
  (disj-id cb-disj-id)
  (branch-idx cb-branch-idx)
  (label cb-label)                  ; e.g., "n₂ = 1"
  (children cb-children))           ; <proof-tree>

(define-record-type <fact-info>
  (make-fact-info label fact theorem deps)
  fact-info?
  (label fi-label)
  (fact fi-fact)
  (theorem fi-theorem)
  (deps fi-deps))

;;; Constructors for tree nodes
(define (pt-empty)
  (%make-proof-tree 'empty #f #f #f #f '() #f))

(define (pt-fact info rest)
  (%make-proof-tree 'fact info rest #f #f '() #f))

(define (pt-case-split disj-id var-name branches)
  (%make-proof-tree 'case-split #f #f disj-id var-name branches #f))

(define (pt-contradiction explanation)
  (%make-proof-tree 'contradiction #f #f #f #f '() explanation))

;;; ============================================================
;;; BUILDING THE PROOF TREE
;;; ============================================================

(define (build-proof-tree env)
  "Build a proof tree from the environment."
  (let* ((facts (env-facts env))
         (meta-map (env-disj-meta env))
         ;; Find essential facts (those contributing to contradictions/goal)
         (essential (get-essential-facts facts env))
         ;; Group by case context
         (grouped (group-by-context essential)))
    (build-tree meta-map '() grouped)))

(define (get-essential-facts facts env)
  "Get only facts that contribute to contradictions or the goal."
  (let* ((fact-map (make-hash-table equal?))
         (essential-labels (make-hash-table equal?)))

    ;; Build label -> fact map
    (for-each (lambda (f)
                (when (fact-label f)
                  (hash-table-set! fact-map (fact-label f) f)))
              facts)

    ;; Find contradictions and trace back
    (for-each (lambda (f)
                (when (eq? (fact-predicate f) 'false)
                  (trace-essential! fact-map (fact-label f) essential-labels)))
              facts)

    ;; Find goal facts and trace back
    (for-each (lambda (ctx)
                (for-each (lambda (f)
                            (when (and (fact-matches-goal? f (env-goal env))
                                       (context-equal? (fact-dis-ancestors f) ctx))
                              (trace-essential! fact-map (fact-label f) essential-labels)))
                          facts))
              (env-goal-combos env))

    ;; Filter and deduplicate
    (let ((seen (make-hash-table equal?)))
      (filter (lambda (f)
                (and (hash-table-ref/default essential-labels (fact-label f) #f)
                     (let ((key (cons (fact-key f)
                                      (sort-alist (hash-table->alist (fact-dis-ancestors f))))))
                       (if (hash-table-ref/default seen key #f)
                           #f
                           (begin (hash-table-set! seen key #t) #t)))))
              facts))))

(define (trace-essential! fact-map label visited)
  "Recursively trace dependencies to find essential facts."
  (when (and label (not (hash-table-ref/default visited label #f)))
    (hash-table-set! visited label #t)
    (let ((fact (hash-table-ref/default fact-map label #f)))
      (when fact
        (for-each (lambda (dep)
                    (trace-essential! fact-map dep visited))
                  (fact-deps fact))))))

(define (context-equal? ctx1 ctx2)
  "Check if two contexts (hash tables) are equal."
  (let ((a1 (sort-alist (hash-table->alist ctx1)))
        (a2 (sort-alist (hash-table->alist ctx2))))
    (equal? a1 a2)))

(define (sort-alist alist)
  "Sort an alist for comparison."
  (sort alist (lambda (a b)
                (string<? (format-pair (car a))
                          (format-pair (car b))))))

(define (format-pair p)
  (string-append (car p) "." (number->string (cdr p))))

(define (group-by-context facts)
  "Group facts by their case context, returns ((context . facts) ...)."
  (let ((groups (make-hash-table equal?)))
    (for-each (lambda (f)
                (let* ((ctx (sort-alist (hash-table->alist (fact-dis-ancestors f))))
                       (existing (hash-table-ref/default groups ctx '())))
                  (hash-table-set! groups ctx (append existing (list f)))))
              facts)
    ;; Sort by context size (base case first)
    (sort (hash-table->alist groups)
          (lambda (a b) (< (length (car a)) (length (car b)))))))

(define (build-tree meta-map current-case grouped-facts)
  "Build tree recursively, grouping by case context."
  (let* ((matching (filter-matching current-case grouped-facts))
         (fact-infos (map fact->info matching))
         (rest (remove-matching current-case grouped-facts)))

    (cond
      ;; Found contradiction
      ((any (lambda (fi) (eq? (fact-predicate (fi-fact fi)) 'false)) fact-infos)
       (build-contradiction-branch fact-infos))

      ;; Look for case split
      ((find-next-split current-case rest)
       => (lambda (split)
            (build-with-case-split meta-map current-case fact-infos rest split)))

      ;; Just facts, no split
      (else
       (fold-right pt-fact (pt-empty) fact-infos)))))

(define (filter-matching current-case grouped)
  "Get facts matching the current case context exactly."
  (let ((entry (assoc current-case grouped)))
    (if entry (cdr entry) '())))

(define (remove-matching current-case grouped)
  "Remove facts matching the current case context."
  (filter (lambda (entry)
            (not (equal? (car entry) current-case)))
          grouped))

(define (fact->info f)
  "Convert a fact to fact-info for display."
  (make-fact-info (fact-label f) f (fact-theorem f) (fact-deps f)))

(define (build-contradiction-branch fact-infos)
  "Build a branch ending in contradiction."
  (if (null? fact-infos)
      (pt-empty)
      (fold-right pt-fact
                  (pt-contradiction "contradiction")
                  (drop-right fact-infos 1))))

(define (build-with-case-split meta-map current-case fact-infos rest split)
  "Build a node with a case split."
  (let* ((disj-id (car split))
         (meta (hash-table-ref/default meta-map disj-id
                                       (make-disj-meta "case" '())))
         (branch-values (disj-meta-branch-values meta))
         (branches
          (map (lambda (idx label)
                 ;; new-case format: (((disj-id . idx) . #t) ...)
                 (let ((new-case (cons (cons (cons disj-id idx) #t) current-case)))
                   (make-case-branch
                    disj-id idx label
                    (build-tree meta-map new-case rest))))
               (iota (length branch-values))
               branch-values)))
    (fold-right pt-fact
                (pt-case-split disj-id (disj-meta-var-name meta) branches)
                fact-infos)))

(define (find-next-split current-case grouped)
  "Find the next disjunction that extends the current case."
  (let loop ((entries grouped))
    (if (null? entries)
        #f
        (let* ((ctx (caar entries))  ; ctx is alist: (((disj-id . idx) . #t) ...)
               ;; Extract just the keys (disj-id . idx) from the alist
               (ctx-keys (map car ctx))
               (current-keys (map car current-case))
               (extensions (filter (lambda (key)
                                     (not (member key current-keys)))
                                   ctx-keys)))
          (if (pair? extensions)
              (car extensions)  ; Return (disj-id . branch-idx)
              (loop (cdr entries)))))))

;;; ============================================================
;;; TREE RENDERING
;;; ============================================================

(define (render-tree env)
  "Render the proof as an ASCII tree."
  (let ((tree (build-proof-tree env))
        (meta-map (env-disj-meta env)))
    (append
     '("" "Proof Structure:" "════════════════════" "")
     (render-node meta-map "" tree)
     (render-summary env))))

(define (render-node meta-map prefix tree)
  "Render a single node of the proof tree."
  (case (pt-kind tree)
    ((empty) '())

    ((contradiction)
     (list (string-append prefix "└─ ⊥ (contradiction)")))

    ((fact)
     (let* ((fi (pt-fact-info tree))
            (fact-str (pp-fact (fi-fact fi)))
            (label-str (or (fi-label fi) "?"))
            (thm-str (if (fi-theorem fi)
                         (string-append "[" (symbol->string (fi-theorem fi)) "]")
                         "[hypothesis]"))
            (line (string-append prefix "• " label-str ": " fact-str " " thm-str)))
       (cons line (render-node meta-map prefix (pt-next-tree tree)))))

    ((case-split)
     (let* ((var-name (pt-var-name tree))
            (header (string-append prefix "┌─ Case split on " var-name ":"))
            (branches (pt-branches tree))
            (total (length branches)))
       (cons header
             (append-map
              (lambda (branch idx)
                (render-branch meta-map prefix total idx branch))
              branches
              (iota total)))))

    (else '())))

(define (render-branch meta-map prefix total idx branch)
  "Render a single branch of a case split."
  (let* ((is-last (= idx (- total 1)))
         (connector (if is-last "└" "├"))
         (child-prefix (string-append prefix (if is-last "  " "│ ")))
         (branch-header (string-append prefix connector "─ "
                                       (cb-label branch) ":")))
    (cons branch-header
          (render-node meta-map child-prefix (cb-children branch)))))

(define (render-summary env)
  "Render the proof summary."
  (let* ((closed (env-closed-branches env))
         (goals (env-goal-combos env))
         (num-branches (+ (length closed) (length goals))))
    (if (and (null? closed) (null? goals))
        '("" "No proof found.")
        (append
         '("" "═══ Proof Summary ═══" "")
         (list (string-append "Proved "
                              (if (null? goals) "contradiction" "goal")
                              " in "
                              (number->string num-branches)
                              " branch"
                              (if (= num-branches 1) "" "es")
                              ":"))
         '("")
         (map (lambda (ctx)
                (string-append "  ✓ "
                               (render-context ctx (env-disj-meta env))))
              (append goals closed))))))

(define (render-context ctx meta-map)
  "Render a case context as a string."
  (if (zero? (hash-table-size ctx))
      "base case"
      (string-join
       (map (lambda (pair)
              (let* ((disj-id (caar pair))
                     (idx (cdar pair))
                     (meta (hash-table-ref/default meta-map disj-id #f)))
                (if meta
                    (string-append (disj-meta-var-name meta) "="
                                   (safe-list-ref (disj-meta-branch-values meta) idx "?"))
                    (string-append disj-id "." (number->string idx)))))
            (hash-table->alist ctx))
       ", ")))

;;; ============================================================
;;; CLEAN LINEAR OUTPUT
;;; ============================================================

(define (render-clean env)
  "Render cleaner linear output with case grouping."
  (let* ((facts (env-facts env))
         (essential (get-essential-facts facts env))
         (grouped (group-by-context essential))
         (meta-map (env-disj-meta env)))
    (append
     (append-map (lambda (group)
                   (render-case-group (car group) (cdr group) meta-map))
                 grouped)
     (render-summary env))))

(define (render-case-group ctx facts meta-map)
  "Render a group of facts with a case header."
  (let ((header (if (null? ctx)
                    '("═══ Hypotheses ═══" "")
                    (list (string-append "═══ Case: "
                                         (render-context-list ctx meta-map)
                                         " ═══")
                          ""))))
    (append header
            (append-map (lambda (f) (render-fact-clean f)) facts))))

(define (render-context-list ctx meta-map)
  "Render a context list (alist) as a string."
  (string-join
   (map (lambda (pair)
          (let* ((disj-id (caar pair))
                 (idx (cdar pair))
                 (meta (hash-table-ref/default meta-map disj-id #f)))
            (if meta
                (string-append (disj-meta-var-name meta) "="
                               (safe-list-ref (disj-meta-branch-values meta) idx "?"))
                (string-append disj-id "." (number->string idx)))))
        ctx)
   ", "))

(define (render-fact-clean fact)
  "Render a single fact with clean formatting."
  (let* ((is-false (eq? (fact-predicate fact) 'false))
         (fact-str (if is-false
                       "⊥ (contradiction)"
                       (pp-fact fact)))
         (label-str (or (fact-label fact) "?"))
         (thm-str (if (fact-theorem fact)
                      (string-append "by " (pretty-theorem-name (fact-theorem fact)))
                      "hypothesis"))
         (dep-str (if (null? (fact-deps fact))
                      ""
                      (string-append " from " (string-join (fact-deps fact) " "))))
         (prefix (if is-false "  ✓ " "  ")))
    (list (string-append prefix label-str " : " fact-str)
          (string-append prefix "    " thm-str dep-str)
          "")))

(define (pretty-theorem-name name)
  "Pretty-print theorem names."
  (case name
    ((sylow) "Sylow's theorem")
    ((single_sylow_normal) "unique Sylow subgroup is normal")
    ((not_simple) "simple ∧ not_simple → ⊥")
    ((counting_contradiction) "element counting")
    ((lagrange) "Lagrange's theorem")
    ((divides_contradiction) "divisibility contradiction")
    ((embed_An) "embedding into Aₙ")
    ((alternating_order) "order of alternating group")
    ((alternating_simple) "Aₙ is simple (n≥5)")
    ((subgroup_index) "subgroup index")
    ((count_order_pk_elements) "counting p^k-order elements")
    ((more_than_one_sylow) "more than one Sylow subgroup")
    ((hypothesis) "hypothesis")
    (else (if (symbol? name) (symbol->string name) "unknown"))))

;;; Utility functions are defined in core.scm
