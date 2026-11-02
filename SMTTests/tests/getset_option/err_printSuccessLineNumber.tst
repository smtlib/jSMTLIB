; A60: the script's own :print-success is answered by jSMTLIB, not sent, so a solver-reported line
; number after it must still be the script's (line 6 here)
(set-option :print-success true)
(set-logic QF_UF)
(declare-fun x () Bool)
(declare-fun x () Bool)
