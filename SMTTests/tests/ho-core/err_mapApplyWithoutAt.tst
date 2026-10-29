; (m t) for a map m is checked as (@ m t); a constant that is not a map takes no arguments
(set-logic ALL)
(declare-const m (-> Int Int))
(declare-const k Int)
(assert (= (m true) 0))
(assert (= (m 0 1) 0))
(assert (= (k 0) 0))
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects ->; z3 4.16.0 and later read -> as Array but have no @.
