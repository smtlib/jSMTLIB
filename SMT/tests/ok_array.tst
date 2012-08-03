; tests OK use of array functions and sort
(set-logic QF_AX)
(declare-sort I 0)
(declare-sort V 0)
(declare-fun a () (Array I V))
(declare-fun i () I)
(declare-fun v () V)
(assert (= v (select a i)))
(assert (= a (store a i v)))
