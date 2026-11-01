; OPTIONS: --relax
; With --relax, jSMTLIB accepts an option set after set-logic that may be set only in start mode
(set-logic QF_UF)
(set-option :produce-models true)
(set-option :produce-assertions true)
(get-option :produce-models)
