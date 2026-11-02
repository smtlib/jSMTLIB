; OPTIONS: --solver generic --pipeline
; The solver closes its output, then writes an error on stderr and exits: that error answers
; check-sat, not "closed its output stream without a response" (A62).
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
