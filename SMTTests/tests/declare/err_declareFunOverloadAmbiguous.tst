; OPTIONS: --relax --solver test
; --relax: f and c overloaded only by result sort: bare uses are ambiguous (an error naming the candidates); as selects one
(set-logic QF_UFLIA)
(declare-sort S 0)
(declare-sort T 0)
(declare-fun f (Int) S)
(declare-fun f (Int) T)
(declare-fun c () S)
(declare-fun c () T)
(assert (= (f 1) (f 1)))
(assert (= ((as f T) 1) ((as f T) 1)))
(assert (= c c))
(assert (= (as c S) (as c S)))
