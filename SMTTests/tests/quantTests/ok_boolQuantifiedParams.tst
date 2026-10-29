; A quantifier over Bool variables only. yices2 rejects every quantifier when run incrementally,
; as jSMTLIB runs it; its adapter case-splits Bool-sorted variables, so yices2 answers this one.
(set-logic ALL)
(declare-fun p () Bool)
(assert (forall ((b Bool) (c Bool)) (or b c p)))
(check-sat)
