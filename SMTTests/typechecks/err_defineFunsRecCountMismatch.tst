; define-funs-rec's declaration list and body list must have the same length --
; distinct from tests/define/err_defineFunsRec_sortMismatch.tst, which covers a body's
; sort not matching its declaration, not a count mismatch between the two lists
(set-logic QF_UF)
(define-funs-rec ((f ((x Bool)) Bool) (g ((x Bool)) Bool)) ((f x)))
