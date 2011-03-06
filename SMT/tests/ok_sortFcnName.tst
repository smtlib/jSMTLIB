; check that sorts and function names do not overlap
(set-logic QF_UF)
(declare-sort A 0)
(declare-fun A () A)
(declare-fun B () A)
(assert (= A B))
(declare-sort B 1)
