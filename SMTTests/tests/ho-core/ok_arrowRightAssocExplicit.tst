; The nested/explicit form of the sort ok_atLeftAssocSugarCombined.tst's
; (-> Int Int Int Bool) sugar abbreviates -- confirms the underlying curried-sort
; machinery itself is fine independent of the :right-assoc sugar.
(set-logic ALL)
(declare-fun f () (-> Int (-> Int Bool)))
; Solver bug (.bad golden): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @.
