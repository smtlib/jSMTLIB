; (_ to_fp eb sb) accepts only one or two arguments
(set-logic ALL)
(assert (= ((_ to_fp 8 24) RNE 1.0 2.0) (_ +zero 8 24)))
