; test scope of define-sort
(set-logic QF_UF)
(define-sort A () Bool)
(push 1)
(define-sort B () Bool)
(pop 1)
(declare-fun xx () B)
