; An assertion over a sort parameter holds for every sort (SMT-LIB 2.7, Remark 13): the
; second assertion gives every sort, U included, two elements, contradicting the first
; (unsat). Treating A as a new sort makes it sat.
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort U 0)
(declare-sort-parameter A)
(assert (forall ((x U) (y U)) (= x y)))
(assert (not (forall ((x A) (y A)) (= x y))))
(check-sat)
