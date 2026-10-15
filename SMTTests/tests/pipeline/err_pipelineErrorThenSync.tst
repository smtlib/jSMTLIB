; OPTIONS: --pipeline
; A solver error among commands sent without waiting, followed by commands that wait: for a
; solver that stops after the error (cvc5, yices2), the waiting commands report that it has
; exited, as without --pipeline.
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x undeclared))
(declare-fun y () Int)
(echo "after the error")
(assert (= y 1))
(check-sat)
(get-value (y))
