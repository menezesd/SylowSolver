;;; theorems.scm - Theorem definitions for group theory
;;;
;;; This module defines the theorems used in proving group-theoretic
;;; properties, particularly those related to Sylow's theorems.

;;; ============================================================
;;; THEOREM TYPES
;;; ============================================================

;;; Standard theorem: fixed premises -> fixed conclusions
(define-record-type <theorem>
  (make-theorem name premises conclusions)
  theorem?
  (name theorem-name)
  (premises theorem-premises)       ; list of <fact> templates
  (conclusions theorem-conclusions)) ; list of <fact> templates

;;; Hyper-theorem: premises + rule function -> computed conclusions
(define-record-type <hyper-theorem>
  (make-hyper-theorem name premises rule)
  hyper-theorem?
  (name hyper-theorem-name)
  (premises hyper-theorem-premises)  ; list of <fact> templates
  (rule hyper-theorem-rule))         ; (matched-facts subst env) -> list of conclusions

;;; Get theorem name (works for both types)
(define (thm-name thm)
  (if (theorem? thm)
      (theorem-name thm)
      (hyper-theorem-name thm)))

;;; Get theorem premises (works for both types)
(define (thm-premises thm)
  (if (theorem? thm)
      (theorem-premises thm)
      (hyper-theorem-premises thm)))

;;; ============================================================
;;; THEOREM TRIGGER INDEX
;;; ============================================================

;;; A trigger index maps (predicate . arity) to theorems that
;;; have a matching premise. This enables O(1) lookup when
;;; a new fact arrives.

(define-record-type <trigger>
  (make-trigger theorem premise-index)
  trigger?
  (theorem trigger-theorem)
  (premise-index trigger-premise-index))

(define (build-trigger-index theorems)
  "Build an index from (pred . arity) -> list of triggers."
  (let ((index (make-hash-table equal?)))
    (for-each
     (lambda (thm)
       (let ((prems (thm-premises thm)))
         (let loop ((i 0) (ps prems))
           (when (pair? ps)
             (let* ((key (fact-key (car ps)))
                    (existing (hash-table-ref/default index key '())))
               (hash-table-set! index key
                                (cons (make-trigger thm i) existing)))
             (loop (+ i 1) (cdr ps))))))
     theorems)
    index))

;;; ============================================================
;;; CLOSING THEOREMS (produce false)
;;; ============================================================

;;; simple(G) + not_simple(G) -> false()
(define thm-simple-contradiction
  (make-theorem
   'not_simple
   (list (make-fact 'simple (list (var "G")))
         (make-fact 'not_simple (list (var "G"))))
   (list (make-fact 'false '()))))

;;; divides(m, n) + not-divisible -> false()
;;; This is handled by a hyper-theorem that checks the math
(define thm-divides-contradiction
  (make-hyper-theorem
   'divides_contradiction
   (list (make-fact 'divides (list (var "m") (var "n"))))
   (lambda (facts subst env)
     (let ((m-arg (subst-ref subst "m"))
           (n-arg (subst-ref subst "n")))
       (if (and (numeric-arg? m-arg) (numeric-arg? n-arg))
           (let ((m (arg-value m-arg))
                 (n (arg-value n-arg)))
             (if (and (> m 0) (not (zero? (modulo n m))))
                 (list (conc-fact (make-fact 'false '())))
                 '()))
           '())))))

;;; ============================================================
;;; SYLOW'S THEOREM
;;; ============================================================

;;; The main Sylow theorem: if p^k divides |G|, then G has a
;;; Sylow p-subgroup, and the number of such subgroups is
;;; congruent to 1 mod p and divides |G|/p^k.

(define thm-sylow
  (make-hyper-theorem
   'sylow
   (list (make-fact 'group (list (var "G")))
         (make-fact 'order (list (var "G") (var "n"))))
   (lambda (facts subst env)
     (let ((g-arg (subst-ref subst "G"))
           (n-arg (subst-ref subst "n")))
       (if (numeric-arg? n-arg)
           (let ((n (arg-value n-arg)))
             (sylow-conclusions g-arg n env))
           '())))))

(define (sylow-conclusions g-arg n env)
  "Generate all Sylow-related conclusions for a group of order n."
  (let ((factorization (prime-factorization n)))
    (append-map
     (lambda (pf)
       (let* ((p (car pf))
              (k (cdr pf))
              (pk (expt p k))
              (m (/ n pk))
              (possible-counts (sylow-counts p m)))
         (if (null? possible-counts)
             '()  ; No valid counts (shouldn't happen)
             (let* ((p-arg (num p))
                    (psub (env-fresh-symbol! env (string-append "P" (number->string p)))))
               (append
                ;; Always true: there exists a Sylow p-subgroup
                (list (conc-fact (make-fact 'sylow_p_subgroup (list psub p-arg g-arg)))
                      (conc-fact (make-fact 'subgroup (list psub g-arg)))
                      (conc-fact (make-fact 'order (list psub (num pk)))))
                ;; Disjunction: num_sylow is one of the possible values
                (if (= (length possible-counts) 1)
                    ;; Only one possibility: emit as fact
                    (list (conc-fact (make-fact 'num_sylow
                                                (list p-arg g-arg (num (car possible-counts))))))
                    ;; Multiple possibilities: emit as disjunction
                    (list (conc-disj
                           (make-disjunction
                            (map (lambda (c)
                                   (make-fact 'num_sylow (list p-arg g-arg (num c))))
                                 possible-counts))))))))))
     factorization)))

;;; Compute valid Sylow counts: n_p ≡ 1 (mod p) and n_p | m
(define (sylow-counts p m)
  "Return list of valid Sylow p-subgroup counts."
  (filter (lambda (c)
            (and (= (modulo c p) 1)
                 (zero? (modulo m c))))
          (divisors m)))

;;; ============================================================
;;; SINGLE SYLOW SUBGROUP THEOREMS
;;; ============================================================

;;; If there's exactly one Sylow p-subgroup, it's normal
(define thm-single-sylow-normal
  (make-theorem
   'single_sylow_normal
   (list (make-fact 'group (list (var "G")))
         (make-fact 'num_sylow (list (var "p") (var "G") (exact "1"))))
   (list (make-fact 'not_simple (list (var "G"))))))

;;; If num_sylow > 1, record that fact
(define thm-more-than-one-sylow
  (make-hyper-theorem
   'more_than_one_sylow
   (list (make-fact 'num_sylow (list (var "p") (var "G") (var "n"))))
   (lambda (facts subst env)
     (let ((n-arg (subst-ref subst "n")))
       (if (and (numeric-arg? n-arg) (> (arg-value n-arg) 1))
           (list (conc-fact (make-fact 'more_than_one_sylow
                                       (list (subst-ref subst "p")
                                             (subst-ref subst "G")))))
           '())))))

;;; ============================================================
;;; LAGRANGE'S THEOREM
;;; ============================================================

;;; |H| divides |G| when H is a subgroup of G
(define thm-lagrange
  (make-theorem
   'lagrange
   (list (make-fact 'subgroup (list (var "H") (var "G")))
         (make-fact 'order (list (var "G") (var "n")))
         (make-fact 'order (list (var "H") (var "m"))))
   (list (make-fact 'divides (list (var "m") (var "n"))))))

;;; ============================================================
;;; SUBGROUP INDEX
;;; ============================================================

;;; [G:H] = |G|/|H|
(define thm-subgroup-index
  (make-hyper-theorem
   'subgroup_index
   (list (make-fact 'subgroup (list (var "H") (var "G")))
         (make-fact 'order (list (var "G") (var "n")))
         (make-fact 'order (list (var "H") (var "m"))))
   (lambda (facts subst env)
     (let ((g-arg (subst-ref subst "G"))
           (h-arg (subst-ref subst "H"))
           (n-arg (subst-ref subst "n"))
           (m-arg (subst-ref subst "m")))
       (if (and (numeric-arg? n-arg) (numeric-arg? m-arg))
           (let ((n (arg-value n-arg))
                 (m (arg-value m-arg)))
             (if (and (> m 0) (zero? (modulo n m)))
                 (list (conc-fact (make-fact 'index
                                             (list g-arg h-arg (num (/ n m))))))
                 '()))
           '())))))

;;; ============================================================
;;; COUNTING ARGUMENTS
;;; ============================================================

;;; Elements of order p^k: Each Sylow p-subgroup contributes
;;; p^k - p^(k-1) elements of order exactly p^k

(define thm-count-pk-elements
  (make-hyper-theorem
   'count_order_pk_elements
   (list (make-fact 'group (list (var "G")))
         (make-fact 'order (list (var "G") (var "n")))
         (make-fact 'num_sylow (list (var "p") (var "G") (var "np")))
         (make-fact 'more_than_one_sylow (list (var "p") (var "G"))))
   (lambda (facts subst env)
     (let ((g-arg (subst-ref subst "G"))
           (n-arg (subst-ref subst "n"))
           (p-arg (subst-ref subst "p"))
           (np-arg (subst-ref subst "np")))
       (if (and (numeric-arg? n-arg)
                (numeric-arg? p-arg)
                (numeric-arg? np-arg))
           (let* ((n (arg-value n-arg))
                  (p (arg-value p-arg))
                  (np (arg-value np-arg))
                  (pk (highest-power-dividing p n))
                  (count (* np (- pk (/ pk p)))))
             (list (conc-fact (make-fact 'order_pk_lower_bound
                                         (list p-arg g-arg (num count))))))
           '())))))

;;; Counting contradiction: sum ALL element bounds for a group.
;;; When a new order_pk_lower_bound is derived, look up all compatible
;;; bounds from the environment and check if total > |G|.
(define thm-counting-contradiction
  (make-hyper-theorem
   'counting_contradiction
   (list (make-fact 'order (list (var "G") (var "n")))
         (make-fact 'order_pk_lower_bound (list (var "p") (var "G") (var "cp"))))
   (lambda (facts subst env)
     (let ((n-arg (subst-ref subst "n"))
           (g-arg (subst-ref subst "G"))
           (trigger-fact (cadr facts)))
       (if (not (numeric-arg? n-arg))
           '()
           (let* ((n (arg-value n-arg))
                  (trigger-ancestors (fact-dis-ancestors trigger-fact))
                  ;; Look up all order_pk_lower_bound facts for this group
                  (all-bounds (env-lookup env (cons 'order_pk_lower_bound 3)))
                  ;; Filter: same group, numeric, compatible ancestors
                  (compatible-bounds
                   (filter
                    (lambda (f)
                      (let ((args (fact-args f)))
                        (and (= (length args) 3)
                             (arg-equal? (cadr args) g-arg)
                             (numeric-arg? (car args))
                             (numeric-arg? (caddr args))
                             (compatible-ancestors? (list trigger-fact f)))))
                    all-bounds))
                  ;; Deduplicate by prime: keep highest bound per prime
                  (best-by-prime (make-hash-table eqv?)))
             ;; Build best bound per prime
             (for-each
              (lambda (f)
                (let* ((p (arg-value (car (fact-args f))))
                       (c (arg-value (caddr (fact-args f))))
                       (existing (hash-table-ref/default best-by-prime p 0)))
                  (when (> c existing)
                    (hash-table-set! best-by-prime p c))))
              compatible-bounds)
             ;; Sum all bounds + 1 for identity
             (let ((total (+ 1 (hash-table-fold best-by-prime
                                                 (lambda (k v acc) (+ v acc))
                                                 0))))
               (if (and (> (hash-table-size best-by-prime) 1)
                        (> total n))
                   (list (conc-fact (make-fact 'false '())))
                   '()))))))))

;;; ============================================================
;;; EMBEDDING IN ALTERNATING GROUPS
;;; ============================================================

;;; A simple group G with n_p Sylow subgroups (n_p > 1) embeds in A_{n_p}
;;; via the conjugation action on Sylow subgroups.
(define thm-embed-alternating
  (make-hyper-theorem
   'embed_An
   (list (make-fact 'num_sylow (list (var "p") (var "G") (var "np")))
         (make-fact 'simple (list (var "G"))))
   (lambda (facts subst env)
     (let ((g-arg (subst-ref subst "G"))
           (np-arg (subst-ref subst "np")))
       (if (and (numeric-arg? np-arg) (> (arg-value np-arg) 1))
           (let ((an (env-fresh-symbol! env "A")))
             (list (conc-fact (make-fact 'subgroup (list g-arg an)))
                   (conc-fact (make-fact 'alternating_group
                                         (list an np-arg)))))
           '())))))

;;; Order of alternating group A_n is n!/2
;;; Skip n > 100 to avoid computing huge factorials
(define thm-alternating-order
  (make-hyper-theorem
   'alternating_order
   (list (make-fact 'alternating_group (list (var "A") (var "n"))))
   (lambda (facts subst env)
     (let ((a-arg (subst-ref subst "A"))
           (n-arg (subst-ref subst "n")))
       (if (and (numeric-arg? n-arg) (<= (arg-value n-arg) 100))
           (let ((n (arg-value n-arg)))
             (list (conc-fact (make-fact 'order
                                         (list a-arg (num (/ (factorial n) 2)))))))
           '())))))

;;; A_n is simple for n >= 5
(define thm-alternating-simple
  (make-hyper-theorem
   'alternating_simple
   (list (make-fact 'alternating_group (list (var "A") (var "n"))))
   (lambda (facts subst env)
     (let ((a-arg (subst-ref subst "A"))
           (n-arg (subst-ref subst "n")))
       (if (and (numeric-arg? n-arg) (>= (arg-value n-arg) 5))
           (list (conc-fact (make-fact 'simple (list a-arg))))
           '())))))

;;; ============================================================
;;; COSET ACTION AND SIMPLE GROUP ACTION
;;; ============================================================

;;; index(G, H, n) -> transitive_action(G, n)
(define thm-coset-action
  (make-theorem
   'coset_action
   (list (make-fact 'index (list (var "G") (var "H") (var "n"))))
   (list (make-fact 'transitive_action (list (var "G") (var "n"))))))

;;; transitive_action(G, n) + simple(G) -> subgroup(G, A_n) + alternating_group(A_n, n)
;;; (A simple group acts faithfully, so embeds in A_n)
(define thm-simple-group-action
  (make-hyper-theorem
   'simple_group_action
   (list (make-fact 'transitive_action (list (var "G") (var "n")))
         (make-fact 'simple (list (var "G"))))
   (lambda (facts subst env)
     (let ((g-arg (subst-ref subst "G"))
           (n-arg (subst-ref subst "n")))
       (if (and (numeric-arg? n-arg) (> (arg-value n-arg) 1))
           (let ((an (env-fresh-symbol! env "A")))
             (list (conc-fact (make-fact 'subgroup (list g-arg an)))
                   (conc-fact (make-fact 'alternating_group (list an n-arg)))))
           '())))))

;;; ============================================================
;;; ALL THEOREMS
;;; ============================================================

(define all-theorems
  (list thm-simple-contradiction
        thm-divides-contradiction
        thm-sylow
        thm-single-sylow-normal
        thm-more-than-one-sylow
        thm-lagrange
        thm-subgroup-index
        thm-count-pk-elements
        thm-counting-contradiction
        thm-embed-alternating
        thm-alternating-order
        thm-alternating-simple
        thm-coset-action
        thm-simple-group-action))

;;; ============================================================
;;; NUMBER THEORY UTILITIES
;;; ============================================================

(define (prime? n)
  "Check if n is prime."
  (and (> n 1)
       (let loop ((i 2))
         (cond
           ((> (* i i) n) #t)
           ((zero? (modulo n i)) #f)
           (else (loop (+ i 1)))))))

(define (prime-factorization n)
  "Return list of (prime . exponent) pairs."
  (let loop ((n n) (p 2) (factors '()))
    (cond
      ((= n 1) (reverse factors))
      ((> (* p p) n)
       (reverse (cons (cons n 1) factors)))
      ((zero? (modulo n p))
       (let count-loop ((n n) (k 0))
         (if (zero? (modulo n p))
             (count-loop (/ n p) (+ k 1))
             (loop n (+ p 1) (cons (cons p k) factors)))))
      (else
       (loop n (+ p 1) factors)))))

(define (divisors n)
  "Return sorted list of all divisors of n."
  (let loop ((i 1) (small '()) (large '()))
    (cond
      ((> (* i i) n)
       (append (reverse small) large))
      ((zero? (modulo n i))
       (if (= i (/ n i))
           (loop (+ i 1) (cons i small) large)
           (loop (+ i 1) (cons i small) (cons (/ n i) large))))
      (else (loop (+ i 1) small large)))))

(define (highest-power-dividing p n)
  "Return the highest power of p that divides n."
  (let loop ((n n) (pk 1))
    (if (zero? (modulo n p))
        (loop (/ n p) (* pk p))
        pk)))

(define (factorial n)
  "Compute n!."
  (if (<= n 1) 1 (* n (factorial (- n 1)))))

(define (gcd a b)
  "Greatest common divisor."
  (if (zero? b) a (gcd b (modulo a b))))
