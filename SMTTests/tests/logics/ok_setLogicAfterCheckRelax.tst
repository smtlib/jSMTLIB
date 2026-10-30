; OPTIONS: --relax
; Under --relax a solver may accept a second set-logic (jSMTLIB's test solver and the Simplify
; adapter do, starting afresh); one it accepts ends sat mode, so get-model is then an error.
; A solver that rejects it, as most do, stays in sat mode with its assertion stack unchanged.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun p () Bool)
(push 1)
(assert p)
(check-sat)
(set-logic QF_UF)
(get-model)
(assert (not p))
(check-sat)
