; Combines both sugars: f's sort is declared using -> :right-assoc sugar (not explicit
; nesting), then applied via @ :left-assoc sugar with more arguments than @'s base
; arity. Reasoning pair as in ok_atLeftAssocSugar.tst.
(set-logic ALL)
(declare-fun f () (-> Int Int Int Bool))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (@ f x y z))
(check-sat)
(assert (not (@ (@ (@ f x) y) z)))
(check-sat)
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @; z3 4.16.0 and later read -> as Array but have no @.
