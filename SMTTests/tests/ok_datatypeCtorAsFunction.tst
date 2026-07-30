; constructors and selectors can be used as function names in subsequent terms
(set-info :smt-lib-version "V2.6")
(set-logic QF_UF)
(declare-datatype Pair ((mk-pair (fst Bool) (snd Bool))))
(declare-const p Pair)
(assert (= p (mk-pair true false)))
(assert (= (fst p) true))
(assert (= (snd p) false))
