; An ill-sorted argument to the n-ary sugar of => (:right-assoc) or and (:left-assoc) is named
; with its own position and sort, including the first argument folded (last for =>, first for and).
(set-logic QF_UF)
(declare-sort U 0)
(declare-fun p () Bool)
(declare-fun u () U)
(assert (=> p p u))
(assert (=> p u p))
(assert (=> u p p))
(assert (and u p p))
(assert (and p u p))
(assert (and p p u))
