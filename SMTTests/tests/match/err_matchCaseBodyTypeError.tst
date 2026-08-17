; a match case's body is type-checked like any other term -- referencing an
; undeclared symbol in one case body must be reported like anywhere else
(set-logic ALL)
(declare-datatype Color ((red) (green) (blue)))
(declare-fun c () Color)
(assert (match c ((red true) (green undeclaredSymbol) (blue false))))
