; declare-fun with malformed arguments
(set-logic QF_UF)
(declare-fun x Bool)
(declare-fun x () A)
(declare-fun x (y z) Bool)
(declare-fun x ((y Bool)(y Bool)) Bool)
(declare-fun x () A A)

