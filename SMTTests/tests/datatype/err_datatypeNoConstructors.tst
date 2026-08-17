; declare-datatypes: a datatype with zero constructors is rejected -- caught
; generically by TypeChecker.validate()'s validateDatatypeGroup before the command is
; dispatched to any solver. Only reachable through the "par" form: the bare grammar
; requires constructor_dec+, so a plain "(declare-datatype D ())" or
; "(declare-datatypes ((D 0)) (()))" is rejected by the parser itself before
; type-checking is ever reached, but a par clause's inner constructor list can be
; syntactically empty.
(set-logic ALL)
(declare-datatypes ((D 1)) ((par (T) ())))
