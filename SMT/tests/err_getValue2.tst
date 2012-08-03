; get-value without check-sat
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun x () Bool)
(get-value (x))
