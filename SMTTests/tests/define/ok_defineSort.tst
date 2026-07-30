; valid define-sort command
(set-logic QF_UF)
(declare-sort Z 1)
(define-sort A () Bool)
(define-sort B (X) (Z X))
(define-sort C () (Z A)) 
