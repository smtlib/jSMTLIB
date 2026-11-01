; OPTIONS: --solver generic
; A stderr line read unfinished with the last reply, before the input ends, is still logged.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
