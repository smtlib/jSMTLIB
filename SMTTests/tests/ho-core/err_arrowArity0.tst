; The -> (arrow) sort constructor requires exactly 2 arguments in its base form (see ok_arrowArity2.tst
; and, for the 3-arg :right-assoc sugar, ok_atLeftAssocSugarCombined.tst). (->) is also a syntax error, a
; parenthesized sort with no parameters: reported, then parsing goes on, so type checking reports the arity.
(set-logic ALL)
(declare-fun f () (->))
