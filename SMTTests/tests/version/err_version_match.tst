; Tests version error: match expression requires SMT-LIB V2.6
(set-info :smt-lib-version 2.5)
(set-logic QF_UF)
(declare-fun x () Bool)
(assert (match x ((y y))))
