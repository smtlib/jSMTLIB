; OPTIONS: --solver altergo --pipeline
; alt-ergo writes nothing for success and exits after an error; with an echo sent after each
; pipelined command, the error is matched to the command that caused it (pop), not the oldest.
(set-logic QF_UF)
(declare-fun p () Bool)
(push 1)
(pop 2)
(assert p)
(check-sat)
