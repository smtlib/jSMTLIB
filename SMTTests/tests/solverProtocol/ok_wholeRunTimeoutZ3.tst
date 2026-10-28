; OPTIONS: --solver z3-4.14.1 -T 5
; z3 reports the whole-run time limit as timeout; later commands answer timeout too.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
(get-model)
(check-sat)
