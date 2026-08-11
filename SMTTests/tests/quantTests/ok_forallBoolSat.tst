(set-logic UFLRA)
(assert (forall ((q Bool)) (or q (not q))))
(check-sat)
