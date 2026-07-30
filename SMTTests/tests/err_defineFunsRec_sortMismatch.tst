; body sort mismatch in define-funs-rec: f declares Bool but first body has sort Int
(set-info :smt-lib-version "V2.5")
(set-logic UFLIA)
(define-funs-rec ((f ((x Int)) Bool) (g ((x Int)) Int)) ((x) (x)))
