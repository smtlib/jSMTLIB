; Tests version error: match expression requires SMT-LIB V2.7
(set-info :smt-lib-version "V2.6")
(set-logic QF_UF)
(declare-fun x () Bool)
(assert (match x ((y y))))
