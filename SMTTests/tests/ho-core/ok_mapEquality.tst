; = on maps is extensional (HO-Core), so equal maps agree at every point
(set-logic ALL)
(declare-const m (-> Int Int))
(declare-const n (-> Int Int))
(assert (= m n))
(assert (not (= (@ m 0) (@ n 0))))
(check-sat)
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects ->; z3 4.16.0 and later read -> as Array but have no @.
