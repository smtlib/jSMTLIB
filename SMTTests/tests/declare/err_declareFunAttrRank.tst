; OPTIONS: --relax --solver test
; --relax: a declare-fun's :left-assoc etc. must fit its rank, as in a theory definition (#217)
(set-logic QF_UFLIA)
(declare-fun f (Int Int) Bool :left-assoc)
(declare-fun g (Int) Int :right-assoc)
(declare-fun h (Int Int) Bool :chainable :pairwise)
(declare-fun k (Int Int) Bool :pairwise 1)
(declare-fun par (A) (p A A Bool :chainable))
