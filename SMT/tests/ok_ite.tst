; checks ite as a term
(set-logic QF_UF)
(declare-sort A 0)
(declare-fun a () A)
(assert (= a (ite true a a)))
