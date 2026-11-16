; OPTIONS: --solver generic
; Structured replies that do not parse are reported as unexpected output: get-assertions, get-value
; and get-assignment (as err_flatRepliesAfterSat.tst, for replies that are not flat).
(set-option :produce-assertions true)
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-assertions)
(get-value (p))
(get-assignment)
