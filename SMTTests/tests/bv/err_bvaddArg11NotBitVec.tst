; An argument sort error at the 11th argument (the ordinal past "tenth")
(set-logic QF_BV)
(declare-const a (_ BitVec 4))
(assert (= a (bvadd a a a a a a a a a a true)))
