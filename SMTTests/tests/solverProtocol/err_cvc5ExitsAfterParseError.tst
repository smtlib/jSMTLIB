; OPTIONS: --solver cvc5-1.3.2
; cvc5 exits after a "Parse Error"; jSMTLIB stops it and reports later commands as unsent.
(set-logic ALL)
(assert QQ)
(declare-const x Int)
(check-sat)
