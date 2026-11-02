; OPTIONS: --solver simplify
; Simplify answers Invalid. when it finds no proof, which means sat only in a logic it decides (#176):
; in QF_LIA the adapter answers unknown, with :reason-unknown incomplete
(set-option :produce-models true)
(set-logic QF_LIA)
(declare-fun x () Int)
(assert (> x 0))
(check-sat)
(get-info :reason-unknown)
(get-model)
(get-value (x))
