; OPTIONS: --relax --solver test
; --relax: a declare-fun symbol overloaded at two signatures; each f in (f (f x)) resolves by its argument's sort
(set-logic QF_UFLIA)
(declare-fun f (Int) Bool)
(declare-fun f (Bool) Int)
(declare-fun x () Int)
(assert (f x))
(assert (= (f (f x)) 5))
(check-sat)
