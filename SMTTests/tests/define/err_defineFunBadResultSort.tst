; define-fun: the declared result sort itself is invalid/unknown -- result.accept(f)
; returns null, so the body expression is never even type-checked (guarded by
; "if (res != null)"), and no "does not match" error is produced either.
(set-logic QF_UF)
(define-fun f () BadSort true)
