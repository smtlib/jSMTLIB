; OPTIONS: --solver z3-4.14.1 -T 5
; The whole-run time limit reported in answer to (get-unsat-assumptions) is a timeout; later commands answer timeout too.
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-unsat-assumptions)
(check-sat)
