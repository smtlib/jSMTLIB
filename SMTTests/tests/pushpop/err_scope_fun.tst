; test scope of declare-fun
(set-logic QF_UF)
(declare-fun x () Bool)
(push 1)
(declare-fun y () Bool)
(pop 1)
(assert y)
