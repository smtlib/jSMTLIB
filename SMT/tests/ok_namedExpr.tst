; testing that named expressions are in scope
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (! p :named P))
(assert (! (and q P) :named PQ))
(assert (and (! p :named PP) (! q :named QQ)))
(assert (or PP QQ))
