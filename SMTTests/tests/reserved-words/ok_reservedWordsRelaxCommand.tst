; OPTIONS: --relax --solver test
; Command names ARE legal as declared symbol names under --relax (see
; org.smtlib.sexpr.Parser.parseSymbol()); companion to err_reservedWord_*.tst (this
; directory), which check the same words WITHOUT --relax (always illegal there) against
; real solvers, and to err_reservedWordsRelaxNonCommand.tst, which checks the non-command
; reserved words that --relax does NOT permit. Replaces the old reservedWordsRelax.scr,
; which spawned 43 separate JVMs (one per word) to check exactly this -- a single
; in-process session covers it just as well.
;
; "--solver test" forces the mock solver regardless of which solver FileTests' own
; (solver, file) parameterization picked: --relax only relaxes jSMTLIB's own client-side
; symbol check, not what gets forwarded to a real solver, whose own parser may still
; reject (or, worse, hang on) a reserved word used as a symbol on its own terms -- this is
; a jSMTLIB parser-level characterization, not something a real solver needs to validate.
(set-logic QF_UF)
(declare-const assert Bool)
(declare-const check-sat Bool)
(declare-const check-sat-assuming Bool)
(declare-const declare-const Bool)
(declare-const declare-datatype Bool)
(declare-const declare-datatypes Bool)
(declare-const declare-fun Bool)
(declare-const declare-sort Bool)
(declare-const declare-sort-parameter Bool)
(declare-const define-const Bool)
(declare-const define-fun Bool)
(declare-const define-fun-rec Bool)
(declare-const define-funs-rec Bool)
(declare-const define-sort Bool)
(declare-const echo Bool)
(declare-const exit Bool)
(declare-const get-assertions Bool)
(declare-const get-assignment Bool)
(declare-const get-info Bool)
(declare-const get-model Bool)
(declare-const get-option Bool)
(declare-const get-proof Bool)
(declare-const get-unsat-assumptions Bool)
(declare-const get-unsat-core Bool)
(declare-const get-value Bool)
(declare-const pop Bool)
(declare-const push Bool)
(declare-const reset Bool)
(declare-const reset-assertions Bool)
(declare-const set-info Bool)
(declare-const set-logic Bool)
(declare-const set-option Bool)
