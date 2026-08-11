(set-logic QF_UF)
(declare-fun p () Bool)
(assert (let ((x p)(y (not p))) (= x (not y)) ))
(check-sat)
