; Issue #37: a push/pop numeral argument far beyond Integer.MAX_VALUE must be rejected with a
; clean error, not silently truncated by BigInteger.intValue()'s low-order-bits wraparound.
(set-logic QF_UF)
(push 99999999999999999999)
(reset)
(set-logic QF_UF)
(push 1)
(pop 99999999999999999999)
(reset)
(set-logic QF_UF)
(push 2)
(pop 2)
