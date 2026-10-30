; OPTIONS: --solver altergo --pipeline
; alt-ergo writes nothing for success; with an echo sent after each pipelined command, an error
; is matched to the command that caused it (pop), not the oldest, and later commands are answered.
(set-logic QF_UF)
(declare-fun p () Bool)
(push 1)
(pop 2)
(assert p)
(check-sat)
