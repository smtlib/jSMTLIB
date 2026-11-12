; OPTIONS: --solver generic
; Flat replies to structured commands (#140, #149; moved from FlatResponseTests, #145): get-assertions
; answered success and get-value answered with an empty line are out of step; get-assignment's
; unsupported is passed on. The generic adapter (Solver_smt) talks to the stub.
(set-option :produce-assertions true)
(set-option :produce-models true)
(set-option :produce-assignments true)
(set-logic QF_UF)
(declare-fun p () Bool)
(check-sat)
(get-assertions)
(get-value (p))
(get-assignment)
