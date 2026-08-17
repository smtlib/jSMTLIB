; (_ to_fp eb sb) applied to a single argument reinterprets a BitVec's bits -- Int is
; not accepted in that one-argument overload
(set-logic ALL)
(declare-fun n () Int)
(assert (= ((_ to_fp 8 24) n) (_ +zero 8 24)))
