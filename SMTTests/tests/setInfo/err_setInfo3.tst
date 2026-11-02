; set-info accepts get-info keywords; get-info :reason-unknown needs an unknown check-sat
(set-info :all-statistics x)
;(get-info :all-statistics) ;; non-deterministic
(set-info :reason-unknown x)
(get-info :reason-unknown)
