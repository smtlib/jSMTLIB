; 7 div 2 is 3. Simplify's adapter translated div as an uninterpreted function and answered
; sat, so it rejects nonlinear integer logics.
(set-logic QF_NIA)
(assert (not (= (div 7 2) 3)))
(check-sat)
