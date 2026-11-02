; #160: a Bool variable is true or false
(set-logic UFLRA)
(assert (forall ((b Bool)) (or (= b true) (= b false))))
(check-sat)
