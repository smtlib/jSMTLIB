; Issue #49: AUFNIRA/AUFLIRA must implicitly coerce an Int-sorted argument to Real (via
; to_real) when an operator's real overload is otherwise the only match -- even when every
; argument is Int (e.g. (/ x x), with no Real-sorted argument anywhere to key the coercion
; retry off of). Mixed Int/Real comparisons already worked before the fix; a genuine sort
; mismatch (Int vs Bool) must still be rejected.
;
; Per SMT-LIB's own AUFNIRA.smt2/AUFLIRA.smt2 :extensions text, "(/ t1 t2) is syntactic
; sugar for (/ (to_real t1) (to_real t2))" unconditionally (unlike the other two extension
; rules, which require a genuine Int/Real mix) -- so this fix is exactly what the standard
; requires, not a permissive extension beyond it. Real solvers mostly disagree: every z3
; version tested and cvc5 (by default) reject this desugaring; only smtinterpol accepts it
; out of the box. See issue #111 for the full empirical survey and analysis.
(set-logic AUFNIRA)
(declare-const x Int)
(assert (= (/ x x) 1.0))
(declare-const y Real)
(assert (< x y))
(declare-const b Bool)
(assert (< x b))
(reset)
(set-logic AUFLIRA)
(assert (= (/ 4 2) 2.0))
