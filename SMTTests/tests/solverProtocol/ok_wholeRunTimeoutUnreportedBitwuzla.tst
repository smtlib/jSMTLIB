; OPTIONS: --solver bitwuzla -T 1
; As ok_wholeRunTimeoutUnreported.tst, for the bitwuzla adapter.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
