; OPTIONS: --solver generic
; The solver closes its output instead of answering get-value.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-value (p))
