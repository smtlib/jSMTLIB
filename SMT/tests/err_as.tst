; tests illegal uses of as identifiers
(set-logic QF_UF)
(assert (= ((as and Bool) true false) false))
