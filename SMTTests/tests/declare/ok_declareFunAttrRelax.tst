; OPTIONS: --relax --solver test
; --relax: a declare-fun with a function attribute; :left-assoc lets myadd take 3 arguments
(set-logic QF_UFLIA)
(declare-fun myadd (Int Int) Int :left-assoc)
(assert (= (myadd 1 2 3) 6))
(check-sat)
