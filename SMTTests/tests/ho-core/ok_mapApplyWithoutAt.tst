; the @ may be omitted: (m t) means (@ m t) for a map m, declared or bound, with @'s
; left-assoc currying (SMT-LIB 2.7 Sec. 3.9)
(set-logic ALL)
(declare-const m (-> Int Int))
(declare-const g (-> Int Int Bool))
(assert (g 0 (m 1)))
(assert (forall ((k (-> Int Int))) (= (k 0) (@ k 0))))
(assert (not (= (m 0) (@ m 0))))
(check-sat)
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects ->; z3 4.16.0 and later read -> as Array but have no @.
