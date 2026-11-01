; OPTIONS: --solver generic --pipeline
; ok_stderrLineUnfinished, pipelined.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
