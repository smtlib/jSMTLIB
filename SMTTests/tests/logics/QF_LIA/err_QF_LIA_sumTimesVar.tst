; QF_LIA: a product whose constant factor is a sum is not linear in jSMTLIB's check
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (= (* (+ 1 1) x) 4))
