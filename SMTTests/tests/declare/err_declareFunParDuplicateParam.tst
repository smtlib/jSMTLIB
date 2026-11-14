; OPTIONS: --relax --solver test
; The sort parameters of a par-polymorphic declare-fun must be distinct, as for define-sort (#209)
(set-logic ALL)
(declare-fun par (X X) (h X X))
