; A par-polymorphic declare-fun's inner (name sort+ attribute*) form requires at least
; a result sort -- see C_declare_fun.parse()'s "Expected at least a result sort" check.
(set-logic QF_UF)
(declare-fun par (A) (f))
