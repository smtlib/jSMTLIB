; lambda is SMT-LIB 2.7; under 2.6 it is an error
(set-info :smt-lib-version 2.6)
(set-logic ALL)
(assert (@ (lambda ((x Int)) true) 1))
