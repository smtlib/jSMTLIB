; A second set-logic command without --relax is an error: SMT-LIB permits set-logic only in
; start mode. The real solvers report it themselves, except Bitwuzla, which accepts it, so its
; adapter reports it (as do jSMTLIB's test solver and the Simplify adapter, in this wording).
(set-logic QF_UF)
(declare-fun x () Bool)
(set-logic QF_UF)
