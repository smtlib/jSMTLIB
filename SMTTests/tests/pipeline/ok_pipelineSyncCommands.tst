; OPTIONS: --pipeline
; Each kind of command that waits for the earlier responses, right after commands sent
; without waiting: the output must stay in order.
(set-logic QF_LIA)
(declare-fun x () Int)
(echo "after declare-fun")
(assert (> x 0))
(get-info :error-behavior)
(assert (< x 5))
(get-option :produce-models)
(declare-fun y () Int)
(set-option :print-success true)
(assert (> y x))
(get-assertions)
(check-sat)
