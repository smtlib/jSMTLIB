; test scope of declare-sort
(set-logic QF_UF)
(declare-sort A 0)
(push 1)
(declare-sort B 0)
(pop 1)
(declare-fun xx () B)
