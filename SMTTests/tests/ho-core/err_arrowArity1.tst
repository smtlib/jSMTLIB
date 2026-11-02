; -> with only one argument -- see err_arrowArity0.tst
(set-logic ALL)
(declare-fun f () (-> Int))
; Solver bug (.bad golden): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @.
