; OPTIONS: --solver z3-4.14.1 -T 5
; The whole-run time limit reported in answer to (get-value (p)) is a timeout; later commands answer timeout too.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
(check-sat)
