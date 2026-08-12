; Tests version error: check-sat-assuming requires literal args in V2.6 and earlier
(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(check-sat-assuming ((and true false)))
