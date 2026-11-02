; OPTIONS: --solver cvc5-1.3.2 --pipeline
; As err_yices2CommandsAfterExit.tst, pipelined: commands sent without waiting, and those that are not.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(assert q)
(declare-fun r () Bool)
(assert r)
(get-value (p))
(echo "hi")
(check-sat)
