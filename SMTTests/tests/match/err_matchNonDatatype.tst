; match error: scrutinee must be a datatype sort
(set-info :smt-lib-version "V2.6")
(set-logic UFLIA)
(declare-fun x () Int)
(assert (match x ((y y))))
