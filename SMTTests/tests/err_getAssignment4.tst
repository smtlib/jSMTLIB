; get-assignment after unsat
(set-option :produce-assignments true)
(set-logic QF_UF)
(assert false)
(check-sat)
(get-assignment)
