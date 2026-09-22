; Issue #21: SymbolTable.hasAttribute(Entry, String) iterated entry.attributes with no null
; check. A plain (non-associative) declared/defined function has attributes == null, so
; calling it with more arguments than its arity (forcing SymbolTable.lookup() to try
; matchAssociative(), whose first line was hasAttribute(entry, ":left-assoc")) threw an
; uncaught NullPointerException instead of a clean "no matching declaration" error.
(set-logic QF_UF)
(declare-fun f (Bool Bool) Bool)
(declare-const x Bool)
(declare-const y Bool)
(declare-const z Bool)
(assert (f x y z))
