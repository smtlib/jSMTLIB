; checks ite as a formula
(set-logic QF_UF)
(declare-fun a () Bool)
(assert (ite true a a))
