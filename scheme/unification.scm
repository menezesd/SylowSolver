;;; unification.scm - Unification and substitution for theorem matching
;;;
;;; This module implements first-order unification for matching
;;; theorem premises against known facts.

;;; ============================================================
;;; SUBSTITUTIONS
;;; ============================================================

;;; A substitution maps variable names to argument values.
;;; We use SRFI-69 hash tables for O(1) lookup.

(define (make-substitution)
  "Create an empty substitution."
  (make-hash-table string=?))

(define (subst-ref subst var-name)
  "Look up a variable in the substitution."
  (hash-table-ref/default subst var-name #f))

(define (subst-set! subst var-name value)
  "Bind a variable in the substitution (mutating)."
  (hash-table-set! subst var-name value))

(define (subst-extend subst var-name value)
  "Create a new substitution with an additional binding."
  (let ((new (hash-table-copy subst)))
    (hash-table-set! new var-name value)
    new))

(define (subst-copy subst)
  "Create a copy of a substitution."
  (hash-table-copy subst))

(define (subst->alist subst)
  "Convert a substitution to an association list."
  (hash-table->alist subst))

;;; ============================================================
;;; ARGUMENT UNIFICATION
;;; ============================================================

;;; Unify a template argument (from a theorem premise) with a
;;; concrete argument (from a known fact).
;;;
;;; Returns: updated substitution, or #f if unification fails

(define (unify-arg template concrete subst)
  "Unify a template argument with a concrete argument."
  (case (arg-type template)
    ;; Variables: bind or check consistency
    ((var)
     (let* ((var-name (arg-value template))
            (existing (subst-ref subst var-name)))
       (cond
         ;; Not yet bound: bind it
         ((not existing)
          (subst-extend subst var-name concrete))
         ;; Already bound: check consistency
         ((arg-equal? existing concrete)
          subst)
         ;; Conflict: fail
         (else #f))))

    ;; Exact arguments: must match the value literally
    ((exact)
     (if (and (or (symbol-arg? concrete) (numeric-arg? concrete))
              (equal? (arg-value template)
                      (if (numeric-arg? concrete)
                          (number->string (arg-value concrete))
                          (symbol->string (arg-value concrete)))))
         subst
         #f))

    ;; Fresh arguments: generate new symbol when theorem fires
    ;; During matching, they match anything
    ((fresh)
     subst)

    ;; Symbols and numbers: must match exactly
    ((sym num)
     (if (arg-equal? template concrete)
         subst
         #f))

    (else #f)))

;;; ============================================================
;;; FACT UNIFICATION
;;; ============================================================

;;; Unify a template fact (from a theorem premise) with a
;;; concrete fact (from the known facts).
;;;
;;; Returns: updated substitution, or #f if unification fails

(define (unify-fact template concrete subst)
  "Unify a template fact with a concrete fact."
  ;; Check predicate name matches
  (and (eq? (fact-predicate template) (fact-predicate concrete))
       ;; Check arity matches
       (= (fact-arity template) (fact-arity concrete))
       ;; Unify each argument
       (unify-args (fact-args template) (fact-args concrete) subst)))

(define (unify-args templates concretes subst)
  "Unify lists of arguments pairwise."
  (cond
    ((null? templates)
     (if (null? concretes) subst #f))
    ((null? concretes)
     #f)
    (else
     (let ((new-subst (unify-arg (car templates) (car concretes) subst)))
       (and new-subst
            (unify-args (cdr templates) (cdr concretes) new-subst))))))

;;; ============================================================
;;; SUBSTITUTION APPLICATION
;;; ============================================================

;;; Apply a substitution to an argument, replacing variables
;;; with their bound values.

(define (apply-subst-arg subst arg env)
  "Apply a substitution to an argument."
  (case (arg-type arg)
    ;; Variables: look up in substitution
    ((var)
     (let ((binding (subst-ref subst (arg-value arg))))
       (or binding arg)))  ; Return original if not bound

    ;; Fresh: generate a new symbol
    ((fresh)
     (env-fresh-symbol! env (arg-value arg)))

    ;; Others: return as-is
    (else arg)))

(define (apply-subst-fact subst template env)
  "Apply a substitution to a fact template, creating a new fact."
  (make-fact
   (fact-predicate template)
   (map (lambda (arg) (apply-subst-arg subst arg env))
        (fact-args template))))

;;; ============================================================
;;; MULTI-PREMISE MATCHING
;;; ============================================================

;;; Match a list of premises against known facts, finding all
;;; ways to satisfy them simultaneously.
;;;
;;; Returns: list of successful substitutions

(define (match-premises premises env subst)
  "Find all ways to match premises against known facts."
  (if (null? premises)
      ;; All premises matched: return the substitution
      (list subst)
      ;; Try to match the first premise
      (let* ((template (car premises))
             (key (fact-key template))
             (candidates (env-lookup env key)))
        (append-map
         (lambda (candidate)
           (let ((new-subst (unify-fact template candidate subst)))
             (if new-subst
                 (match-premises (cdr premises) env new-subst)
                 '())))
         candidates))))

;;; Match premises, but one of them (the trigger) is already matched.
;;; This is used in incremental matching when a new fact arrives.

(define (match-remaining-premises before-trigger after-trigger env subst)
  "Match premises excluding the trigger, which is already matched."
  (match-premises (append before-trigger after-trigger) env subst))

;;; ============================================================
;;; COMPATIBILITY CHECKING
;;; ============================================================

;;; Check that a set of facts don't use incompatible disjunction branches.
;;; Two facts are incompatible if they depend on different branches of
;;; the same disjunction.

(define (compatible-ancestors? facts)
  "Check that facts don't mix incompatible disjunction branches."
  (let ((seen (make-hash-table equal?)))
    (call/cc
     (lambda (return)
       (for-each
        (lambda (f)
          (hash-table-walk
           (fact-dis-ancestors f)
           (lambda (key val)
             (let ((label (car key))
                   (idx (cdr key)))
               (let ((existing (hash-table-ref/default seen label 'none)))
                 (cond
                   ((eq? existing 'none)
                    (hash-table-set! seen label idx))
                   ((not (= existing idx))
                    (return #f))))))))  ; Incompatible!
        facts)
       #t))))  ; All compatible

;;; Merge the dis-ancestors from multiple facts
(define (merge-ancestors facts)
  "Merge disjunction ancestors from multiple facts."
  (let ((result (make-hash-table equal?)))
    (for-each
     (lambda (f)
       (hash-table-walk
        (fact-dis-ancestors f)
        (lambda (k v) (hash-table-set! result k v))))
     facts)
    result))
