; OPTIONS: --pipeline --nosuccess
; With 'success' suppressed from the command line, only the other responses are printed.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(push 1)
(assert (< x 0))
(check-sat)
(pop 1)
