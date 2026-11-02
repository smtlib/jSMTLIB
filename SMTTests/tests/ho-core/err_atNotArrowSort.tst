; @'s first argument must have a -> (arrow) sort -- see ok_hoApplyBasic.tst for why
; ALL is the only logic this is reachable under
(set-logic ALL)
(declare-fun f () Int)
(declare-fun x () Int)
(assert (@ f x))
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @; z3 4.16.0 and later read -> as Array but have no @.
