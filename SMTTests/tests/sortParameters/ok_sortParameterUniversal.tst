; An assertion over a sort parameter holds at every sort (SMT-LIB 2.7, 4.2.4): its
; instance at Bool makes f the identity on Bool, contradicting the second assertion
; (unsat). Treating A as a new sort makes (f b) ill-sorted.
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort-parameter A)
(declare-fun f (A) A)
(assert (forall ((x A)) (= (f x) x)))
(declare-const b Bool)
(assert (= (f b) (not b)))
(check-sat)
