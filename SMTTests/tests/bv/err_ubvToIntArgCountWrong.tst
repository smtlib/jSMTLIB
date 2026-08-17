; ubv_to_int/sbv_to_int take exactly one BitVec argument
(set-logic ALL)
(declare-fun x () (_ BitVec 4))
(declare-fun y () (_ BitVec 4))
(assert (= 0 (ubv_to_int x y)))
