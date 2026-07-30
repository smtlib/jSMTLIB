; mutually recursive define-funs-rec
(set-info :smt-lib-version "V2.5")
(set-logic QF_UF)
(define-funs-rec ((f ((x Bool)) Bool) (g ((x Bool)) Bool)) ((g x) (f x)))
