; (as f S) on a left-assoc application with more than two arguments: S must be the result sort
(set-logic QF_UFLIA)
(assert (= ((as + Int) 1 2 3) 6))
(assert (= ((as + Bool) 1 2 3) 6))
