;;; load.scm - Load all Sylow solver modules
;;;
;;; Usage: mit-scheme --load load.scm
;;;    or: (load "load.scm") from the scheme directory

(display "Loading Sylow Solver for MIT Scheme...")
(newline)

(load "core.scm")
(display "  ✓ core.scm         - Core data types")
(newline)

(load "unification.scm")
(display "  ✓ unification.scm  - Unification & substitution")
(newline)

(load "theorems.scm")
(display "  ✓ theorems.scm     - Theorem definitions")
(newline)

(load "solver.scm")
(display "  ✓ solver.scm       - Forward chaining solver")
(newline)

(load "amb.scm")
(display "  ✓ amb.scm          - Non-deterministic choice (call/cc)")
(newline)

(load "solver-amb.scm")
(display "  ✓ solver-amb.scm   - Amb-based solver variant")
(newline)

(load "proof-tree.scm")
(display "  ✓ proof-tree.scm   - Proof tree rendering")
(newline)

(load "main.scm")
(display "  ✓ main.scm         - Entry point & examples")
(newline)

(newline)
(display "Sylow Solver loaded successfully!")
(newline)
(display "Type (help) for usage information.")
(newline)
(newline)
