; @ with only one argument -- see err_atArity0.tst
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(assert (@ f))
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @; z3 4.16.0 and later read -> as Array but have no @.
