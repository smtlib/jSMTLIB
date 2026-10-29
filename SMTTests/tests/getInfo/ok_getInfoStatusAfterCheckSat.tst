; get-info :status after check-sat. :status is not a standard get-info flag (SMT-LIB 2.6/2.7
; Fig. 3.9), so a conforming answer is unsupported or a get_info_response such as (:status sat),
; never a bare sat.
(set-logic QF_UF)
(declare-fun p () Bool)
(assert p)
(check-sat)
(get-info :status)
