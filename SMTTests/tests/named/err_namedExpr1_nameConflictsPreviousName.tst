; a :named symbol must not conflict with a previously used :named symbol
(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (! p :named P))
(assert (! q :named P))
