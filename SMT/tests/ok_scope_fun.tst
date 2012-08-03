; test scope of declare-fun
(set-logic QF_UF)
(declare-fun x () Bool)
(push 1)
(declare-fun y () Bool)
(assert (and x y))
(pop 1)
(assert x)
(declare-fun y () Bool)
