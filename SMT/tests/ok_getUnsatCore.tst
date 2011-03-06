; get-unsat-core after sat/unknown
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(assert (! false :named F))
(check-sat)
(get-unsat-core)
