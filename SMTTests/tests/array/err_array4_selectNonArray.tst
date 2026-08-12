; select applied to a user-declared 2-arity sort that is not the Array theory sort
(set-logic QF_UF)
(declare-sort I 0)
(declare-sort V 0)
(declare-sort AA 2)
(declare-fun a () (AA I V))
(declare-fun i () I)
(declare-fun v () V)
(assert (= v (select a i)))
