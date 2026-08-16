; < is :chainable for Real. 1.0 < 2.0 < 3.0 is true; 1.0 < 3.0 < 2.0 is false
; (3.0 < 2.0 fails) -- pure constants, trivial to decide.
(set-logic QF_LRA)
(assert (< 1.0 2.0 3.0))
(check-sat)
(assert (< 1.0 3.0 2.0))
(check-sat)
