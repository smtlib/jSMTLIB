; (_ to_fp eb sb) applied to two arguments requires a RoundingMode first argument
(set-logic ALL)
(declare-fun bl () Bool)
(assert (= ((_ to_fp 8 24) bl 1.0) (_ +zero 8 24)))
