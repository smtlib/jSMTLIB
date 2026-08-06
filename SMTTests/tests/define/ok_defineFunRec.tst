; simple self-recursive define-fun-rec

(set-logic QF_UF)
(define-fun-rec f ((x Bool)) Bool (f x))
