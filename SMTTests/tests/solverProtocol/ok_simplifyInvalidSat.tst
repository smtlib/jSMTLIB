; OPTIONS: --solver simplify
; In QF_UF, which Simplify decides, Invalid. means sat (#176); :reason-unknown is not available
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(get-info :reason-unknown)
