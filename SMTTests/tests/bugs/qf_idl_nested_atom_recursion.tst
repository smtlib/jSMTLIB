; Issue #44: QF_IDL.validExpression()'s shape-restriction visitor used to return immediately
; for and/or/not/implies without recursing into their arguments, so an invalid IDL atom
; nested inside an "and" (a difference's arguments must both be symbols, not a symbol and a
; numeral) was never validated. Fixed by recursing into these connectives' arguments too.
;
; This restriction is jSMTLIB's own client-side reading of QF_IDL's :language text -- every
; real solver tested (z3, cvc5, yices2, smtinterpol) accepts (- x 1) freely and defers to
; its own native arithmetic solving instead of enforcing the narrower canonical-IDL-atom
; shape, so the bare .out/.err goldens are the real-solver consensus; Solver_test's own
; (stricter) rejection is captured separately in .out.test/.err.test.
(set-logic QF_IDL)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x y) (>= (- x 1) y)))
