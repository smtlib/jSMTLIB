; A :named term must be closed; a let-bound variable is closed only if its bound expression is (#205 item 32).
; Covers what err_namedExpr2.tst does not: a bound expression, a chain of lets, and a let that rebinds
; the quantified name.
(set-logic ALL)
(declare-fun p () Bool)
(assert (forall ((q Bool)) (let ((r (and q p))) (! r :named N1)))) ; error - r is bound to an open term
(assert (forall ((q Bool)) (let ((r q)) (let ((s r)) (! s :named N2))))) ; error - s is r is q
(assert (forall ((q Bool)) (let ((r q)) (! (and r p) :named N3)))) ; error
(assert (forall ((q Bool)) (let ((r p)) (! (and r q) :named N4)))) ; error - q is free in the named term
(assert (forall ((q Bool)) (let ((q p)) (! q :named N5)))) ; OK - q is rebound to p
(assert (forall ((q Bool)) (let ((r p)) (let ((s r)) (! s :named N6))))) ; OK
