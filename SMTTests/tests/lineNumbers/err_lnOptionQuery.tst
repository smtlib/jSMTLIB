; #58: the error below is reported at its own line, after a get- command for which some adapters query an option first
(set-logic QF_UF)
(check-sat)
(get-assignment)
(assert z)
