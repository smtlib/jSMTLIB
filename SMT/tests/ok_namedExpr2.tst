; testing that named expressions are in scope
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(push 1)
(assert (! p :named P))
(assert (! (and q P) :named PQ))
(pop 1)
(assert (! p :named P))
