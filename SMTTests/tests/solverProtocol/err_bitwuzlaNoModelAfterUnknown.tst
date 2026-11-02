; OPTIONS: --solver bitwuzla
; bitwuzla 0.9.1 writes nothing for get-model or get-value after check-sat returns unknown, so the
; adapter answers an error itself; the solver keeps running (the echo is answered).
(set-option :produce-models true)
(set-logic QF_BV)
(declare-const x (_ BitVec 4))
(check-sat)
(get-model)
(get-value (x))
(echo "alive")
