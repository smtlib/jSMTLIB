; define-fun: a parameter's declared sort is invalid/unknown -- checkFcn's per-parameter
; loop records the error but does not break, and the later result/body check is
; entirely skipped (guarded by f.result.isEmpty()), so only this one error is reported,
; not a cascading "undeclared x" error from the body.
(set-logic QF_UF)
(define-fun f ((x BadSort)) Bool true)
