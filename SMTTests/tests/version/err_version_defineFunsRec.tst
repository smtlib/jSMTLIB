; Tests version error: define-funs-rec requires SMT-LIB V2.5
(set-info :smt-lib-version 2.0)
(define-funs-rec ((f ((x Int)) Int)) (x))
