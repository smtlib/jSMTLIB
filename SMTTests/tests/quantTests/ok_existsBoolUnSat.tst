(set-logic UFLRA)
(assert (exists ((q Bool)) (and q (not q))))
(check-sat)
