; OPTIONS: --relax --solver test
; A par-polymorphic declare-fun with a trailing attribute after its sorts -- exercises
; C_declare_fun.parse()'s parseAttributeSequence() call inside the par branch (the only
; way to reach that particular call; an ordinary, non-par declare-fun's attributes are
; parsed by the other branch instead).
(set-logic QF_UF)
(declare-fun par (A) (f A A :left-assoc))
