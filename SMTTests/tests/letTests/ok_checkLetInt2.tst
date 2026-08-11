(set-logic QF_LIA)
(declare-fun c () Int)
(assert (let ((x 5)(y (+ c 1)) (z (- c 1))) (= (- y z) 3)))
(check-sat)
