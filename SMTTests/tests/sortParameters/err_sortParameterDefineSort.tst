; A sort definition may contain no global sort parameter; its own parameters shadow one (SMT-LIB 2.7,
; 4.2.3: define-sort): S is an error, T is not (#178)
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort-parameter A)
(define-sort S () (Array A Int))
(define-sort T (A) (Array A Int))
