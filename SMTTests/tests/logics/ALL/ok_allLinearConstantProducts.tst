; Under ALL, products with one non-constant factor are linear, so Simplify's adapter accepts them:
; a negated numeral counts as a constant, a sum does not. x = -2 satisfies both.
(set-logic ALL)
(declare-fun x () Int)
(assert (= (* (- 2) x) 4))
(assert (= (* (+ x 1) 2) (- 2)))
(check-sat)
