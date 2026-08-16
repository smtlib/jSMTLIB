; >= is :chainable for Real. 3.0 >= 2.0 >= 1.0 is true; 3.0 >= 1.0 >= 2.0 is false
; (1.0 >= 2.0 fails) -- pure constants, trivial to decide.
(set-logic QF_LRA)
(assert (>= 3.0 2.0 1.0))
(check-sat)
(assert (>= 3.0 1.0 2.0))
(check-sat)
