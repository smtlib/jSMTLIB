; A declaration the solver rejects changes nothing, so the solver stays in sat mode and
; answers get-value and get-model about the last check
(set-option :produce-models true)
(set-logic QF_UF)
(declare-const x Bool)
(assert x)
(check-sat)
(declare-const x Bool)
(get-value (x))
(get-model)
