; binary - is :left-assoc for Real. (3.0 - 5.0) - 2.0 = -4.0 -- pure constants.
(set-logic QF_LRA)
(assert (= (- 3.0 5.0 2.0) (- 4.0)))
(check-sat)
(assert (= (- 3.0 5.0 2.0) (- 3.0)))
(check-sat)
