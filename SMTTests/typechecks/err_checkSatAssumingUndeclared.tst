; check-sat-assuming type-checks each assumption -- an undeclared symbol is an error
; here for the same reason as err_checkSatAssumingBadSort.tst
(set-logic QF_UF)
(check-sat-assuming (y))
