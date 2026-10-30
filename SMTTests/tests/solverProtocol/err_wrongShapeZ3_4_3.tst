; OPTIONS: --solver z3-4.3
; As err_wrongShape.tst, for the z3-4.3 adapter's own response paths. The adapter sends a priming
; set-option first and answers get-option itself. The wrong reply to the first check-sat is not
; success: on Windows the adapter (Solver_z3_4_3_2) drops success lines before a check-sat result.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun q () Bool)
(declare-fun p () Bool)
(declare-sort S 0)
(check-sat)
(check-sat)
(get-value (p))
(get-model)
(get-value (p))
