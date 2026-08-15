; match error: scrutinee must be a datatype sort
(set-logic ALL)
(declare-fun x () Int)
(assert (match x ((y y))))
