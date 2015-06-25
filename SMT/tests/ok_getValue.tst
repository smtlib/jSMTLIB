; get-value after sat
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun x () Bool)
(assert (= x false))
(check-sat)
(get-value (x))
