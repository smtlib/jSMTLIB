; symbol already defined when define-fun-rec is used
(set-info :smt-lib-version "V2.5")
(set-logic QF_UF)
(declare-fun f (Bool) Bool)
(define-fun-rec f ((x Bool)) Bool (f x))
