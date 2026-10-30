; A constant of a sort parameter's sort is ambiguous, so each use must give its sort with
; as (SMT-LIB 2.7, 3.6.3): the first assertion is an error, the others are well sorted
; (sat). Treating A as a new sort accepts the first and rejects the others.
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort-parameter A)
(declare-const c A)
(assert (= c c))
(assert (= (as c Int) 1))
(assert (as c Bool))
(check-sat)
