; get-unsat-core after an assertionset command
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(assert true)
(check-sat)
(push 1)
(get-unsat-core)
