; get-info :status after set-info :status, before any check-sat. The standard says set-info and
; get-info are unrelated, so a conforming answer is unsupported or a get_info_response such as
; (:status sat), never an error or a bare sat.
(set-logic QF_UF)
(set-info :status sat)
(get-info :status)
