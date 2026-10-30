; OPTIONS: --solver z3-4.14.1 -T 1
; The whole-run limit ends the solver between commands, and no report of that is read (as on Windows CI):
; a command that finds the process gone after the limit has passed answers timeout, as do later ones.
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
