; @ (HO-Core function application) requires exactly 2 arguments in its base form --
; see ok_hoApplyBasic.tst for the base 2-arg case and ok_atLeftAssocSugar.tst for
; the 3-arg :left-assoc sugar case. (@) is also a syntax error, an application with no
; arguments: the parser reports it and goes on, so type checking reports the arity too.
(set-logic ALL)
(assert (@))
