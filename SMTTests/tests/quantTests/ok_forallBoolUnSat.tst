(set-info :smt-lib-version 2.0)
(set-logic UF)
(assert (forall ((q Bool)) (not q)))
(check-sat)
