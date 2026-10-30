; OPTIONS: --solver generic
; The solver writes a line on stderr just before its reply on stdout, and another just after it,
; read with the next reply: each reply answers its command, and the stderr lines are diagnostic.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
