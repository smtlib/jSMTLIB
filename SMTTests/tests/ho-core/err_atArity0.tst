; @ (HO-Core function application) requires exactly 2 arguments in its base form --
; see ok_hoApplyBasic.tst for the base 2-arg case and ok_atLeftAssocSugar.tst for
; the 3-arg :left-assoc sugar case. (@) parses fine -- FcnExpr allows an empty argument
; list syntactically -- and is rejected only at type-checking.
(set-logic ALL)
(assert (@))
