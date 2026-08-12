; select's second argument must match the array's index sort
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort V 0)
(declare-fun i () I)
(declare-fun v () V)
(declare-fun a () (Array I V))
(assert (= i (select a a)))
