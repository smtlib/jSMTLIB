; OPTIONS: --solver generic
; #149's shape check without --pipeline: each response of the wrong kind is an error. The
; generic adapter sends a priming set-option first, and a get-option before each get- command.
; An empty response to a get- command is accepted (yices2 2.6.5 gives one for an empty model).
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun q () Bool)
(declare-fun p () Bool)
(push 1)
(check-sat)
(check-sat)
(get-value (p))
(get-value (p))
(get-model)
(get-value (p))
