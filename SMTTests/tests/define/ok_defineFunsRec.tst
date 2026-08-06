; mutually recursive define-funs-rec

(set-logic QF_UF)
(define-funs-rec ((f ((x Bool)) Bool) (g ((x Bool)) Bool)) ((g x) (f x)))
