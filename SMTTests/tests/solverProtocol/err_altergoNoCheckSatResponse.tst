; OPTIONS: --solver altergo
; alt-ergo writes nothing for success; a check-sat answered by nothing before the echo that follows
; it has no response.
(set-logic QF_UF)
(check-sat)
