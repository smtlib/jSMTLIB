; Further options that may be set only in start mode, i.e. before set-logic (SMT-LIB 4.1.7);
; err_setOptionsAfterLogic.tst has the others
(set-logic QF_UF)
(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :produce-unsat-cores true)
(set-option :produce-assignments true)
(set-option :produce-unsat-assumptions true)
(set-option :random-seed 5)
