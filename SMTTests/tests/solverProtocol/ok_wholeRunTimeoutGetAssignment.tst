; OPTIONS: --solver z3-4.14.1 -T 5
; The whole-run time limit reported in answer to (get-assignment) is a timeout; later commands answer timeout too.
; The stub's "true" answers the (get-option :produce-assignments) z3's adapter sends first.
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-assignment)
(check-sat)
