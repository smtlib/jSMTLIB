; declare-datatype: the same selector name used twice within one datatype group,
; across two different constructors (as opposed to err_datatypeAlreadyDefined.tst's
; clash with a pre-existing symbol)
(set-logic ALL)
(declare-datatype D ((c1 (a Bool)) (c2 (a Bool))))
