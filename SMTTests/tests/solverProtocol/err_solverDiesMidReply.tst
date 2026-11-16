; OPTIONS: --solver generic
; A solver that writes part of a reply, then an error on standard error, and dies: the error
; answers the command.
(set-logic QF_UF)
(check-sat)
