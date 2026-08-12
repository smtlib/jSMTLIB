; a :named symbol that fails (due to conflict) inside a larger expression must not be registered
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (! p :named P))
(assert (and (! p :named PP) (! q :named P)))
(assert PP)
