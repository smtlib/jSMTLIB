; body sort mismatch in define-funs-rec: f declares Bool but first body has sort Int
(set-logic AUFLIA)
(define-funs-rec ((f ((x Int)) Bool) (g ((x Int)) Int)) ((x) (x)))
