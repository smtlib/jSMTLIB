; A let binding whose term is ill-sorted
(set-logic QF_LIA)
(assert (let ((y (+ 1 true))) (> y 0)))
