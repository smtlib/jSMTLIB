; OPTIONS: --solver generic --pipeline
; The solver stops while commands are pipelined: the first pending one reports the closed
; stream, the rest report that the process has exited.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(assert p)
(check-sat)
