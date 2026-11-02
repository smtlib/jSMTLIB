; OPTIONS: --solver generic
; A stderr line read unfinished with a reply, then not finished before exit, is still logged.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(exit)
