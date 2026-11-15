; Each :named term must be closed by itself: d's term refers to x, bound outside it but inside c's (#225)
(set-logic ALL)
(declare-sort U 0)
(assert (! (forall ((x U)) (! (= x x) :named d)) :named c))
