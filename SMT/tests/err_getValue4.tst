; get-value after unsat
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun x () Bool)
(assert false)
(check-sat)
(get-value (x))
