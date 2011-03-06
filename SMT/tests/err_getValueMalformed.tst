; malformed get-value commands
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun x () Bool)
(assert true)
(check-sat)
(get-value)
(get-value x)
(get-value x y)
(get-value (x) ) ; OK
(get-value (x) x)
(get-value () )
