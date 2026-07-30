; tests normal use of get-value, though it is not supported
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun x () Bool)
(get-value (x))
