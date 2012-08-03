; testing that named expr are in scope
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (! p :named q)) ; conflicts with existing name
(assert (! p :named P)); OK
(assert (! q :named P)) ; conflicts
(declare-fun P () Bool) ; conflicts
(assert (and (! p :named PP) (! q :named P))) ; second conflicts, first should be withdrawn
(assert PP) ; should not exist
