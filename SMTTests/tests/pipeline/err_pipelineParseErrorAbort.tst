; OPTIONS: --pipeline --abort
; As err_pipelineParseError, but the run stops at the error, after the earlier responses.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(assert (> x #z1))
(declare-fun y () Int)
(check-sat)
