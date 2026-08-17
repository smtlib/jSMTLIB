; (_ to_fp eb sb) applied to a single BitVec argument requires the BitVec's width to
; be exactly eb+sb
(set-logic ALL)
(declare-fun b () (_ BitVec 16))
(assert (= ((_ to_fp 8 24) b) (_ +zero 8 24)))
