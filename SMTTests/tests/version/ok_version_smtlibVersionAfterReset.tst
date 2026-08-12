; :smt-lib-version is allowed immediately after a reset command, since reset
; conceptually returns to the state right after start (not explicitly
; addressed by the standard, but a reasonable reading of it).
(set-logic QF_UF)
(reset)
(set-info :smt-lib-version 2.7)
(set-logic QF_UF)
