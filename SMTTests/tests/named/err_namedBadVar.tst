; ported from TypeCheck.checkBadNamed -- type-checking still runs inside a :named
; subexpression, not just at the top level
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun p () Bool)
(declare-fun q () X)
(assert (and (! p :named P) (! (not t) :named Q)))
