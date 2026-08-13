; :reason-unknown is only valid when the last check-sat result was "unknown";
; it is not gated by set-logic having been issued
(get-info :reason-unknown)
(set-logic QF_UF)
(get-info :reason-unknown)
