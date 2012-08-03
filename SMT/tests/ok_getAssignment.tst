; get-assignment after unsat
(set-option :produce-assignments true)
(set-logic QF_UF)
(assert (! true :named T))
(check-sat)
(get-assignment)
