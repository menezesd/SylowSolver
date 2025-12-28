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
         (make-fact 'order (list (var "G") (var "n")))
         (make-fact 'simple (list (var "G"))))
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

;;; Counting contradiction: if sum of element counts > |G|, contradiction
(define thm-counting-contradiction
  (make-hyper-theorem
   'counting_contradiction
   (list (make-fact 'group (list (var "G")))
         (make-fact 'order (list (var "G") (var "n")))
         (make-fact 'order_pk_lower_bound (list (var "p") (var "G") (var "cp")))
         (make-fact 'order_pk_lower_bound (list (var "q") (var "G") (var "cq"))))
   (lambda (facts subst env)
     (let ((n-arg (subst-ref subst "n"))
           (p-arg (subst-ref subst "p"))
           (q-arg (subst-ref subst "q"))
           (cp-arg (subst-ref subst "cp"))
           (cq-arg (subst-ref subst "cq")))
       (if (and (numeric-arg? n-arg)
                (numeric-arg? p-arg)
                (numeric-arg? q-arg)
                (numeric-arg? cp-arg)
                (numeric-arg? cq-arg)
                (not (= (arg-value p-arg) (arg-value q-arg))))
           (let ((n (arg-value n-arg))
                 (cp (arg-value cp-arg))
                 (cq (arg-value cq-arg)))
             ;; +1 for identity element
             (if (> (+ cp cq 1) n)
                 (list (conc-fact (make-fact 'false '())))
                 '()))
           '())))))

;;; ============================================================
;;; EMBEDDING IN ALTERNATING GROUPS
;;; ============================================================

;;; A simple group G embeds in A_n where n = [G:H] for any subgroup H
(define thm-embed-alternating
  (make-hyper-theorem
   'embed_An
   (list (make-fact 'simple (list (var "G")))
         (make-fact 'index (list (var "G") (var "H") (var "k"))))
   (lambda (facts subst env)
     (let ((g-arg (subst-ref subst "G"))
           (k-arg (subst-ref subst "k")))
       (if (and (numeric-arg? k-arg) (>= (arg-value k-arg) 3))
           (let ((an (env-fresh-symbol! env "A")))
             (list (conc-fact (make-fact 'alternating_group
                                         (list an k-arg)))
                   (conc-fact (make-fact 'subgroup (list g-arg an)))))
           '())))))

;;; Order of alternating group A_n is n!/2
(define thm-alternating-order
  (make-hyper-theorem
   'alternating_order
   (list (make-fact 'alternating_group (list (var "A") (var "n"))))
   (lambda (facts subst env)
     (let ((a-arg (subst-ref subst "A"))
           (n-arg (subst-ref subst "n")))
       (if (numeric-arg? n-arg)
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
        thm-alternating-simple))

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
  "Return list of all divisors of n."
  (let loop ((i 1) (divs '()))
    (cond
      ((> (* i i) n) (reverse divs))
      ((zero? (modulo n i))
       (if (= i (/ n i))
           (loop (+ i 1) (cons i divs))
           (loop (+ i 1) (cons (/ n i) (cons i divs)))))
      (else (loop (+ i 1) divs)))))

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
