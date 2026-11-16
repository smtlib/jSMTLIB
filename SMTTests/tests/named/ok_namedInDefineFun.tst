; A closed term in a define-fun body may be :named (SMT-LIB 2.7, 4.1.6); the definition still holds.
; The label is not used afterwards: jSMTLIB does not define it (see the coverage 2026-11-16 report).
(set-logic ALL)
(declare-fun x () Int)
(define-fun c () Bool (! (> x 0) :named p))
(assert c)
(assert (< x 0))
(check-sat)
