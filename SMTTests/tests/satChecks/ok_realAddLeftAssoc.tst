; + is :left-assoc for Real, same mechanism as Int (see ok_add3argsSat.tst/ok_add3argsUnSat.tst).
; 3.0 + 5.0 + 2.0 = 10.0 -- pure constants, no nonlinear reasoning needed.
(set-logic QF_LRA)
(assert (= (+ 3.0 5.0 2.0) 10.0))
(check-sat)
(assert (= (+ 3.0 5.0 2.0) 11.0))
(check-sat)
