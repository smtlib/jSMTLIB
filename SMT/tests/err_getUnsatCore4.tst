; get-unsat-core after sat/unknown
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(assert true)
(check-sat)
(get-unsat-core)
