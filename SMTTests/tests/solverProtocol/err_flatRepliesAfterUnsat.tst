; OPTIONS: --solver generic
; As err_flatRepliesAfterSat.tst, after unsat: get-unsat-core answered success is out of step;
; get-unsat-assumptions's unsupported is passed on.
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(check-sat)
(get-unsat-core)
(get-unsat-assumptions)
