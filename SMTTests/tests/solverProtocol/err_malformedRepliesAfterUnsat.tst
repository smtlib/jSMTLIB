; OPTIONS: --solver generic
; As err_malformedRepliesAfterSat.tst, after unsat: get-unsat-core and get-unsat-assumptions replies
; that do not parse, and an unsat core holding a term that is not a name.
(set-option :produce-unsat-cores true)
(set-option :produce-unsat-assumptions true)
(set-logic QF_UF)
(check-sat)
(get-unsat-core)
(get-unsat-assumptions)
(get-unsat-core)
