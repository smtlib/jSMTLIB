; check types in the get-value commands
(set-option :produce-models true)
(set-logic QF_UF)
(declare-sort A 0)
(declare-fun x () A)
(declare-fun y () Bool)
(assert true)
(check-sat)
(get-value (x y (and x y) ))
