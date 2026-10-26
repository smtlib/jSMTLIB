; OPTIONS: --relax --solver test
; --relax: a par-polymorphic declare-fun, used at Int and at Bool; :chainable lets it take 3 arguments
(set-logic QF_UFLIA)
(declare-fun par (A) (myeq A A Bool :chainable))
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (myeq a b 5))
(assert (myeq p q true))
(check-sat)
