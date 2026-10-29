; OPTIONS: --solver cvc5-1.3.2 -T 5
; cvc5 reports the whole-run time limit on standard error and aborts; jSMTLIB answers timeout.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(check-sat)
