; A real strictly between 0 and 1 exists. Simplify reasons over integers and answered unsat,
; so its adapter rejects logics with reals.
(set-logic QF_LRA)
(declare-fun r () Real)
(assert (and (< 0 r) (< r 1)))
(check-sat)
