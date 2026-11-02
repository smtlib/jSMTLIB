; get-value terms are held to the logic's restrictions, as assert terms are
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-const x Int)
(check-sat)
(get-value (x (+ x 1)))
; nonlinear term
(get-value ((* x x)))
; quantifier in a QF_ logic
(get-value ((forall ((y Int)) (> y x))))
