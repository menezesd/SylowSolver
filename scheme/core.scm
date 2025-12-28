;;; core.scm - Core data types for the Sylow solver
;;;
;;; This module defines the fundamental data structures:
;;; - Arguments (symbols, variables, numbers, etc.)
;;; - Facts (predicates with arguments)
;;; - Disjunctions (case splits)
;;; - Conclusions (theorem outputs)

;;; ============================================================
;;; SRFI IMPORTS
;;; ============================================================
;;; Requires: SRFI-9 (define-record-type)
;;;           SRFI-69 (hash-tables)

;;; ============================================================
;;; ARGUMENTS
;;; ============================================================

;;; An argument to a predicate can be:
;;; - 'sym: A concrete symbol (e.g., G, H, P)
;;; - 'var: A pattern variable to be unified (e.g., ?x)
;;; - 'num: A numeric value (e.g., 60, 2, 5)
;;; - 'exact: Must match literally (e.g., *foo)
;;; - 'fresh: Generates a new symbol when theorem fires

(define-record-type <arg>
  (make-arg type value)
  arg?
  (type arg-type)
  (value arg-value))

;;; Constructors for different argument types
(define (sym s)
  "Create a symbol argument."
  (make-arg 'sym (if (symbol? s) s (string->symbol s))))

(define (var v)
  "Create a variable argument for pattern matching."
  (make-arg 'var (if (string? v) v (symbol->string v))))

(define (num n)
  "Create a numeric argument."
  (make-arg 'num n))

(define (exact e)
  "Create an exact-match argument."
  (make-arg 'exact (if (string? e) e (symbol->string e))))

(define (fresh f)
  "Create a fresh-symbol argument (generates new symbol when fired)."
  (make-arg 'fresh (if (string? f) f (symbol->string f))))

;;; Predicates for argument types
(define (variable? arg)
  (and (arg? arg) (eq? (arg-type arg) 'var)))

(define (symbol-arg? arg)
  (and (arg? arg) (eq? (arg-type arg) 'sym)))

(define (numeric-arg? arg)
  (and (arg? arg) (eq? (arg-type arg) 'num)))

(define (exact-arg? arg)
  (and (arg? arg) (eq? (arg-type arg) 'exact)))

(define (fresh-arg? arg)
  (and (arg? arg) (eq? (arg-type arg) 'fresh)))

;;; Display an argument as a string
(define (arg-display arg)
  (case (arg-type arg)
    ((sym) (symbol->string (arg-value arg)))
    ((var) (string-append "?" (arg-value arg)))
    ((num) (number->string (arg-value arg)))
    ((exact) (string-append "*" (arg-value arg)))
    ((fresh) (string-append "_" (arg-value arg)))))

;;; Compare arguments for equality
(define (arg-equal? a b)
  (and (eq? (arg-type a) (arg-type b))
       (equal? (arg-value a) (arg-value b))))

;;; Get the raw value for substitution purposes
(define (arg-raw-value arg)
  (case (arg-type arg)
    ((sym) (symbol->string (arg-value arg)))
    ((var) (arg-value arg))
    ((num) (arg-value arg))
    ((exact) (arg-value arg))
    ((fresh) (arg-value arg))))

;;; ============================================================
;;; FACTS
;;; ============================================================

;;; A fact is a predicate applied to arguments, with metadata
;;; for tracking its provenance in the proof.

(define-record-type <fact>
  (%make-fact predicate args label theorem deps dis-ancestors useful)
  fact?
  (predicate fact-predicate)                              ; symbol
  (args fact-args)                                        ; list of <arg>
  (label fact-label fact-label-set!)                      ; string or #f
  (theorem fact-theorem fact-theorem-set!)                ; symbol or #f
  (deps fact-deps fact-deps-set!)                         ; list of labels
  (dis-ancestors fact-dis-ancestors fact-dis-ancestors-set!)  ; hash-table
  (useful fact-useful fact-useful-set!))                  ; boolean

;;; Create a new fact
(define (make-fact predicate args)
  (%make-fact predicate args #f #f '() (make-hash-table equal?) #f))

;;; Create a hypothesis (initial fact)
(define (hypothesis predicate args)
  (let ((f (make-fact predicate args)))
    (fact-theorem-set! f 'hypothesis)
    f))

;;; Fact arity
(define (fact-arity f)
  (length (fact-args f)))

;;; Fact key for indexing: (predicate . arity)
(define (fact-key f)
  (cons (fact-predicate f) (fact-arity f)))

;;; Pretty-print a fact
(define (pp-fact f)
  (string-append
   (symbol->string (fact-predicate f))
   "("
   (string-join (map arg-display (fact-args f)) ", ")
   ")"))

;;; Check if two facts match (same predicate and args)
(define (fact-equal? f1 f2)
  (and (eq? (fact-predicate f1) (fact-predicate f2))
       (= (length (fact-args f1)) (length (fact-args f2)))
       (every arg-equal? (fact-args f1) (fact-args f2))))

;;; Copy a fact (for creating derived facts)
(define (copy-fact f)
  (%make-fact (fact-predicate f)
              (fact-args f)
              #f
              #f
              '()
              (hash-table-copy (fact-dis-ancestors f))
              #f))

;;; ============================================================
;;; DISJUNCTIONS
;;; ============================================================

;;; A disjunction represents a case split: exactly one of the
;;; alternative facts is true, but we don't know which.
;;; The proof must succeed in ALL branches.

(define-record-type <disjunction>
  (%make-disjunction label facts dis-ancestors)
  disjunction?
  (label disj-label disj-label-set!)
  (facts disj-facts)                    ; list of <fact>
  (dis-ancestors disj-dis-ancestors))   ; hash-table: (label . idx) -> #t

(define (make-disjunction facts)
  (%make-disjunction #f facts (make-hash-table equal?)))

;;; ============================================================
;;; CONCLUSIONS
;;; ============================================================

;;; A conclusion is what a theorem produces: either a single
;;; fact or a disjunction of possibilities.

(define-record-type <conclusion>
  (make-conclusion type content)
  conclusion?
  (type conclusion-type)      ; 'fact or 'disjunction
  (content conclusion-content))

(define (conc-fact f)
  "Create a fact conclusion."
  (make-conclusion 'fact f))

(define (conc-disj d)
  "Create a disjunction conclusion."
  (make-conclusion 'disjunction d))

(define (conclusion-facts conc)
  "Extract facts from a conclusion."
  (case (conclusion-type conc)
    ((fact) (list (conclusion-content conc)))
    ((disjunction) (disj-facts (conclusion-content conc)))))

;;; ============================================================
;;; DISJUNCTION METADATA
;;; ============================================================

;;; Metadata for displaying disjunctions nicely
(define-record-type <disj-meta>
  (make-disj-meta var-name branch-values)
  disj-meta?
  (var-name disj-meta-var-name)
  (branch-values disj-meta-branch-values))

;;; Infer metadata from a disjunction's facts
(define (infer-disj-meta facts)
  (if (null? facts)
      (make-disj-meta "?" '())
      (let* ((pred (fact-predicate (car facts)))
             (all-args (map fact-args facts))
             (varying-idx (find-varying-index all-args)))
        (make-disj-meta
         (make-var-name pred varying-idx (fact-args (car facts)))
         (if varying-idx
             (map (lambda (f)
                    (arg-display (list-ref (fact-args f) varying-idx)))
                  facts)
             (map number->string (iota (length facts))))))))

(define (find-varying-index args-lists)
  "Find the index of the first argument position that varies across facts."
  (and (pair? args-lists)
       (pair? (car args-lists))
       (let ((width (length (car args-lists))))
         (let loop ((i 0))
           (if (>= i width)
               #f
               (let ((col (map (lambda (args) (list-ref args i)) args-lists)))
                 (if (all-same? col)
                     (loop (+ i 1))
                     i)))))))

(define (all-same? lst)
  "Check if all elements in the list are equal."
  (or (null? lst)
      (null? (cdr lst))
      (let ((first (car lst)))
        (every (lambda (x) (arg-equal? first x)) (cdr lst)))))

(define (make-var-name pred varying-idx args)
  "Create a nice variable name for display."
  (cond
    ((and (eq? pred 'num_sylow) (eqv? varying-idx 2))
     (string-append "n" (subscript-string (arg-display (car args)))))
    ((and (eq? pred 'sylow_order) (eqv? varying-idx 2))
     (string-append "ord" (subscript-string (arg-display (car args)))))
    (varying-idx
     (string-append "x" (subscript-string (number->string varying-idx))))
    (else "case")))

(define (subscript-string s)
  "Convert digits to subscript characters."
  (list->string
   (map (lambda (c)
          (case c
            ((#\0) #\x2080)  ; ₀
            ((#\1) #\x2081)  ; ₁
            ((#\2) #\x2082)  ; ₂
            ((#\3) #\x2083)  ; ₃
            ((#\4) #\x2084)  ; ₄
            ((#\5) #\x2085)  ; ₅
            ((#\6) #\x2086)  ; ₆
            ((#\7) #\x2087)  ; ₇
            ((#\8) #\x2088)  ; ₈
            ((#\9) #\x2089)  ; ₉
            (else c)))
        (string->list s))))

;;; ============================================================
;;; UTILITY FUNCTIONS
;;; ============================================================

(define (string-join strings sep)
  "Join a list of strings with a separator."
  (if (null? strings)
      ""
      (fold-left (lambda (acc s)
                   (string-append acc sep s))
                 (car strings)
                 (cdr strings))))

(define (fold-left f init lst)
  (if (null? lst)
      init
      (fold-left f (f init (car lst)) (cdr lst))))

(define (any pred lst)
  "Check if predicate holds for any element."
  (and (pair? lst)
       (or (pred (car lst))
           (any pred (cdr lst)))))

(define (every pred . lsts)
  "Check if predicate holds for all elements. Supports multiple lists (SRFI-1 style)."
  (cond
    ((null? lsts)
     #t)
    ((null? (cdr lsts))
     ;; Single list case
     (let ((lst (car lsts)))
       (or (null? lst)
           (and (pred (car lst))
                (every pred (cdr lst))))))
    (else
     ;; Multiple lists case - apply pred to corresponding elements
     (let loop ((lists lsts))
       (cond
         ((any null? lists) #t)  ; Any list exhausted - done
         (else
          (and (apply pred (map car lists))
               (loop (map cdr lists)))))))))

(define (iota n)
  "Generate list (0 1 2 ... n-1)."
  (let loop ((i 0) (acc '()))
    (if (>= i n)
        (reverse acc)
        (loop (+ i 1) (cons i acc)))))

(define (hash-table-copy ht)
  "Create a copy of a hash table."
  (let ((new (make-hash-table (hash-table-equivalence-function ht))))
    (hash-table-walk ht
                     (lambda (k v)
                       (hash-table-set! new k v)))
    new))

(define (hash-table-for-each ht proc)
  "Apply proc to each key-value pair in the hash table."
  (hash-table-walk ht proc))

(define (hash-table->alist ht)
  "Convert a hash table to an association list."
  (let ((result '()))
    (hash-table-walk ht
                     (lambda (k v)
                       (set! result (cons (cons k v) result))))
    result))

(define (hash-table-size ht)
  "Get the number of entries in a hash table."
  (let ((count 0))
    (hash-table-walk ht (lambda (k v) (set! count (+ count 1))))
    count))

;;; List utilities used throughout the codebase

(define (take lst n)
  "Take first n elements from a list."
  (if (or (null? lst) (<= n 0))
      '()
      (cons (car lst) (take (cdr lst) (- n 1)))))

(define (drop lst n)
  "Drop first n elements from a list."
  (if (or (null? lst) (<= n 0))
      lst
      (drop (cdr lst) (- n 1))))

(define (drop-right lst n)
  "Drop the last n elements from a list."
  (take lst (max 0 (- (length lst) n))))

(define (find pred lst)
  "Find first element satisfying predicate."
  (cond
    ((null? lst) #f)
    ((pred (car lst)) (car lst))
    (else (find pred (cdr lst)))))

(define (filter pred lst)
  "Filter list by predicate."
  (let loop ((lst lst) (acc '()))
    (if (null? lst)
        (reverse acc)
        (if (pred (car lst))
            (loop (cdr lst) (cons (car lst) acc))
            (loop (cdr lst) acc)))))

(define (filter-map f lst)
  "Map f over lst, keeping only non-#f results."
  (let loop ((lst lst) (acc '()))
    (if (null? lst)
        (reverse acc)
        (let ((result (f (car lst))))
          (if result
              (loop (cdr lst) (cons result acc))
              (loop (cdr lst) acc))))))

(define (append-map f . lsts)
  "Map f over list(s) and append results. Supports multiple lists (SRFI-1 style)."
  (apply append (apply map f lsts)))

(define (fold-right f init lst)
  "Right fold over a list."
  (if (null? lst)
      init
      (f (car lst) (fold-right f init (cdr lst)))))

(define (safe-list-ref lst idx default)
  "Safe list reference with default value."
  (if (and (>= idx 0) (< idx (length lst)))
      (list-ref lst idx)
      default))

(define (sort lst less?)
  "Sort a list using insertion sort."
  (define (insert x sorted)
    (cond
      ((null? sorted) (list x))
      ((less? x (car sorted)) (cons x sorted))
      (else (cons (car sorted) (insert x (cdr sorted))))))
  (fold-right insert '() lst))
