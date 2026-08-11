(set-info :smt-lib-version "V2.0")
(set-logic UF)
(assert (forall ((q Bool)) (not q)))
(check-sat)
