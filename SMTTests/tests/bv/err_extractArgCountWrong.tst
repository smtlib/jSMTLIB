; (_ extract i j) takes exactly one BitVec argument
(set-logic QF_BV)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (= x ((_ extract 3 0) x y)))
