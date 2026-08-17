; declare-datatype: the same constructor name used twice within one datatype group
; (as opposed to err_datatypeAlreadyDefined.tst's clash with a pre-existing symbol)
(set-logic ALL)
(declare-datatype D ((ctor (a Bool)) (ctor (b Bool))))
