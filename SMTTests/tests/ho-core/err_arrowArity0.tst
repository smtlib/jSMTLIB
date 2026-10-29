; The -> (arrow) sort constructor requires exactly 2 arguments in its base form --
; see ok_arrowArity2.tst for the base 2-arg case and ok_atLeftAssocSugarCombined.tst
; for the 3-arg :right-assoc sugar case.
(set-logic ALL)
(declare-fun f () (->))
; Solver bug (.bad golden): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @.
