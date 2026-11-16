; (_ divisible n) is not among QF_IDL's atoms (#234)
(set-logic QF_IDL)
(declare-const x Int)
(assert ((_ divisible 3) x))
