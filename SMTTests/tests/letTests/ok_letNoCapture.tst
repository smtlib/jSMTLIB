(set-logic LIA)
(declare-fun x () Int)
(assert (let ((t x)) (exists ((x Int)) (not (= x t)))))
(check-sat)
