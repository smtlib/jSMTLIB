; OPTIONS: --solver generic
; #172: every attribute of a multi-attribute get-info reply is kept, including one without a value.
(get-info :version)
; In an :all-statistics reply every number is masked, whatever the statistic is called; names are kept.
(get-info :all-statistics)
