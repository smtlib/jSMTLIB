; check the array axioms
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort V 0)
(declare-fun a () (Array I V))
(declare-fun i () I)
(declare-fun j () I)
(declare-fun v () V)

(push 1)
(assert (not (= v (select (store a i v) i))))
(check-sat) ; should be unsat
(pop 1)

(push 1)
(assert (not (= (select a i) (select a j))))
(assert (= i j))
(check-sat) ; should be unsat
(pop 1)

(push 1)
(assert (not (= i j)))
(assert (not (= v (select a i))))
(assert (not (= (select a i) (select (store a j v) i))))
(check-sat) ; should be unsat
(pop 1)
