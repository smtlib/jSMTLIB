; Issue #20: TypeChecker.visit(IAttributedExpr) recorded an error when a :named attribute's
; value wasn't an ISymbol, but fell through to an unconditional cast anyway, throwing
; ClassCastException (a non-symbol value, e.g. a numeral) or NullPointerException (a bare,
; valueless :named colliding with another null-keyed entry). Fixed by returning immediately
; after recording the "Expected a symbol after :named" error instead of falling through.
(set-logic QF_UF)
(assert (! true :named 5))
(assert (! true :named :named))
