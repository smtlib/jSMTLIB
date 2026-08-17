; 'as' disambiguation where the qualifying sort itself is invalid/unknown -- visit(IAsIdentifier)
; just delegates to the qualifier sort's own check (the identifier's overload is resolved
; later, in the parent IFcnExpr), so this returns null before overload resolution is even
; attempted. See err_as_unknownIdentifier.tst/err_as_userSortNotOverloaded.tst for the
; separate case of a valid sort that the identifier isn't overloaded to.
(set-logic QF_UFLIA)
(assert (= ((as + BadSort) 4 3) 1))
