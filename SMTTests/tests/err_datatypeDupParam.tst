; declare-datatypes: duplicate sort parameter in par clause
(set-info :smt-lib-version "V2.6")
(set-logic QF_UF)
(declare-datatypes ((Pair 2)) ((par (X X) ((pair (a X) (b X))))))
