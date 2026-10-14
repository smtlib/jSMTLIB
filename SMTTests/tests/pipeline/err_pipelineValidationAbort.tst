; OPTIONS: --pipeline --abort
; As err_pipelineValidationError, but the run stops at the error, after the earlier responses.
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(define-fun f ((a Int) (a Int)) Int a)
(declare-fun y () Int)
(check-sat)
