(set-logic QF_UF)
(declare-fun p () Bool)
(assert (let ((x p)(y (not p))) (= x y) ))
(check-sat)
