; OPTIONS: --relax --solver test
; --relax: a par-polymorphic :right-assoc declare-fun, applied correctly and with each of
; the two arguments of a step mismatched
(set-logic ALL)
(declare-fun par (A) (r (Array Int A) (Array Int A) (Array Int A) :right-assoc))
(declare-const a (Array Int Bool))
(assert (= a (r a a a)))
(assert (= a (r a 1 a)))
(assert (= a (r a a 5)))
