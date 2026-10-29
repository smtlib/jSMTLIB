; OPTIONS: --solver generic
; The solver closes its output instead of answering get-assignment.
(set-option :produce-assignments true)
(set-logic QF_UF)
(assert (! true :named a))
(check-sat)
(get-assignment)
