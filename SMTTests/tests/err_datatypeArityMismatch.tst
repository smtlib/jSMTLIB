; declare-datatypes: arity k does not match number of sort parameters in par clause
(set-info :smt-lib-version "V2.6")
(set-logic QF_UF)
(declare-datatypes ((Pair 2)) ((par (X) ((pair (a X))))))
