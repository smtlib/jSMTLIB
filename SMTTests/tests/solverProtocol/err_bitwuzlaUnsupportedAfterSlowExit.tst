; OPTIONS: --solver bitwuzla
; The adapter answers define-fun-rec unsupported without sending it. bitwuzla exits after its
; error, here 300 ms later, as a slow process might; the adapter stops it when it reads the error,
; so the command answers that the solver has exited, as when pipelining (#214).
(set-logic ALL)
(assert true)
(define-fun-rec f ((x Int)) Int x)
(check-sat)
