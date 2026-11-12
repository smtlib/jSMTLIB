; OPTIONS: --solver altergo -T 2
; At its whole-run limit alt-ergo answers the running check-sat unknown, then writes (error "timeout")
; and is ended by a signal (#189); jSMTLIB answers timeout, and reports no unexpected output.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(check-sat)
