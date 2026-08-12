; Tests version error: _ wildcard in match patterns requires SMT-LIB V2.7
(set-info :smt-lib-version 2.6)
(set-logic QF_UF)
(declare-datatype Color ((red) (green) (blue)))
(declare-fun x () Color)
(assert (match x ((_ true))))
