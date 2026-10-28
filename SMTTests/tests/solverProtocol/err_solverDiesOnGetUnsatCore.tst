; OPTIONS: --solver generic
; The solver closes its output instead of answering get-unsat-core.
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(assert false)
(check-sat)
(get-unsat-core)
