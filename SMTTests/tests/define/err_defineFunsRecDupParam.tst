; define-funs-rec: a parameter name repeated in one function's parameter list is an error, as for define-fun
(set-logic QF_UF)
(declare-sort A 0)
(define-funs-rec ((f ((x Bool) (x A)) Bool)) ((and x true)))
