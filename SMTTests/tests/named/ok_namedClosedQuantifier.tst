; A quantified formula is closed, so it may be named: its bound variable is not free in it (#225)
(set-logic ALL)
(declare-sort U 0)
(assert (! (forall ((x U)) (= x x)) :named c))
