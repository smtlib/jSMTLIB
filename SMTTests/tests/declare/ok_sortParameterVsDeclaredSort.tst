; A sort parameter stands for every sort, a declared sort for one new sort (SMT-LIB 2.7,
; Remark 12): only U is made a singleton in the first check (sat), every sort, Bool
; included, in the second (unsat). Treating A as a new sort makes the second sat.
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort U 0)
(declare-sort-parameter A)
(push 1)
(assert (forall ((x U) (y U)) (= x y)))
(check-sat)
(pop 1)
(push 1)
(assert (forall ((x A) (y A)) (= x y)))
(check-sat)
(pop 1)
