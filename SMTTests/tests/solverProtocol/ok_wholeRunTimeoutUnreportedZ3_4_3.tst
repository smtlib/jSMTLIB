; OPTIONS: --solver z3-4.3 -T 1
; As ok_wholeRunTimeoutUnreported.tst, for the z3-4.3 adapter.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
