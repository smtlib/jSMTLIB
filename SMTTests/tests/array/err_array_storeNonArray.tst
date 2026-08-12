; store applied to arguments that are not an array sort
(set-logic QF_UF)
(declare-sort I 0)
(declare-sort V 0)
(declare-fun a () I)
(declare-fun i () I)
(declare-fun v () V)
(assert (= a (store a i v)))
