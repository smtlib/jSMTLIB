; OPTIONS: --solver z3-4.3
; As err_wrongShape.tst, for the z3-4.3 adapter's own response paths. The adapter sends a priming
; set-option first and answers get-option itself. No push: on Windows the adapter (Solver_z3_4_3_2)
; follows push with an echo.
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
