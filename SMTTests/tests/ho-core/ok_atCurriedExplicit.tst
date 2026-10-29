; The explicit/nested form of application, (@ (@ f x) y) -- confirms partial
; application (@ f x) correctly gets an arrow-sorted result usable in further @ and =.
; Also a genuine reasoning pair: having pinned (@ f x) = h, (@ h y) and the negation
; of the fully-nested (@ (@ f x) y) can't both hold.
(set-logic ALL)
(declare-fun f () (-> Int (-> Int Bool)))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun h () (-> Int Bool))
(assert (= (@ f x) h))
(assert (@ h y))
(check-sat)
(assert (not (@ (@ f x) y)))
(check-sat)
; Solver bugs (.bad goldens): cvc5 has no HO-Core under ALL (only under its own HO_ logic
; prefix), so it rejects -> and @; z3 4.16.0 and later read -> as Array but have no @.
