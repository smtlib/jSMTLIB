; OPTIONS: --solver generic
; The solver closes its output instead of answering get-unsat-assumptions.
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-fun p () Bool)
(assert (not p))
(check-sat-assuming (p))
(get-unsat-assumptions)
