; @'s second argument must match the arrow sort's domain -- see ok_hoApplyBasic.tst
; for why ALL is the only logic this is reachable under
(set-logic ALL)
(declare-fun f () (-> Int Bool))
(declare-fun y () Bool)
(assert (@ f y))
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @; z3 4.16.0 and later read -> as Array but have no @.
