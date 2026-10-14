; OPTIONS: --pipeline
; Changing the regular output channel after commands sent without waiting: their responses
; must still go to the channel in effect when they were sent.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(set-option :regular-output-channel "stderr")
(declare-fun y () Int)
(check-sat)
(set-option :regular-output-channel "stdout")
(assert (> y 0))
(check-sat)
