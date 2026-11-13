; A datatype's selector sorts may contain only the sort parameters of its own par, so none in a datatype
; without par (SMT-LIB 2.7, 4.2.3: declare-datatypes): D and L are errors, M is not (#178)
(set-info :smt-lib-version 2.7)
(set-logic ALL)
(declare-sort-parameter A)
(declare-datatype D ((mk (f A))))
(declare-datatype L (par (X) ((nil) (cons (hd A) (tl (L X))))))
(declare-datatype M (par (A) ((nil2) (cons2 (hd2 A) (tl2 (M A))))))
