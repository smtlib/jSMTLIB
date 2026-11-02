; OPTIONS: --pipeline
; Pipelined, a declaration the solver rejects changes nothing, so the solver stays in unsat
; mode and answers get-unsat-core about the last check
(set-option :produce-unsat-cores true)
(set-logic QF_UF)
(declare-const x Bool)
(assert (! x :named a1))
(assert (! (not x) :named a2))
(check-sat)
(declare-const x Bool)
(get-unsat-core)
