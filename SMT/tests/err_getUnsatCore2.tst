; get-unsat-core without a check-sat
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(get-unsat-core)
