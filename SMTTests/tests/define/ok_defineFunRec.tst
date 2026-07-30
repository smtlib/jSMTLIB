; simple self-recursive define-fun-rec
(set-info :smt-lib-version "V2.5")
(set-logic QF_UF)
(define-fun-rec f ((x Bool)) Bool (f x))
