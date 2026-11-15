; OPTIONS: --solver bitwuzla --pipeline
; The adapter answers define-fun-rec unsupported without sending it; pipelined, bitwuzla's
; earlier error and exit are read first, so it answers that the solver has exited, as when
; not pipelining (#214). The stub exits 300 ms after its error, as a slow process might.
(set-logic ALL)
(assert true)
(define-fun-rec f ((x Int)) Int x)
(check-sat)
