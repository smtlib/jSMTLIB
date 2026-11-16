; OPTIONS: --solver z3-4.14.1 -T 5
; The whole-run time limit reported in answer to (get-unsat-core) is a timeout; later commands answer timeout too.
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-unsat-core)
(check-sat)
