; OPTIONS: --solver generic --pipeline
; err_stderrLineContinued, pipelined: the unended stderr line is read when pipelining, and listen()
; finishes it for get-value.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
