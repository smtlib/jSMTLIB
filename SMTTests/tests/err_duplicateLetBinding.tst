; duplicate binding in let
(set-logic QF_LIA)
(assert (let ((x 0)(x 1)) (= x 0)))
