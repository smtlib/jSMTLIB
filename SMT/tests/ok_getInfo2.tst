; get-info that depends on check-sat
(set-logic QF_UF)
(assert true)
(check-sat)
(get-option :all-statistics)
(get-option :reason-unknown)

