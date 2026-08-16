; * is :left-assoc for Real. 3.0 * 5.0 * 2.0 = 30.0 -- pure constants, so this is
; constant folding, not nonlinear reasoning about free variables.
(set-logic QF_LRA)
(assert (= (* 3.0 5.0 2.0) 30.0))
(check-sat)
(assert (= (* 3.0 5.0 2.0) 31.0))
(check-sat)
