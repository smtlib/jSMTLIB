; / is :left-assoc for Real. (6.0 / 3.0) / 2.0 = 1.0 -- dividing by constants stays
; linear, so this needs no nonlinear reasoning.
(set-logic QF_LRA)
(assert (= (/ 6.0 3.0 2.0) 1.0))
(check-sat)
(assert (= (/ 6.0 3.0 2.0) 2.0))
(check-sat)
