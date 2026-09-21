; OPTIONS: --relax --solver test
; Non-command reserved words remain illegal as declared symbol names even under --relax
; (see org.smtlib.sexpr.Parser.parseSymbol()); companion to err_reservedWord_*.tst (this
; directory), which check the same illegality WITHOUT --relax against real solvers, and to
; ok_reservedWordsRelaxCommand.tst, which checks the command-name words that --relax DOES
; permit. Replaces the old reservedWordsRelax.scr, which spawned 43 separate JVMs (one per
; word) to check exactly this -- a single in-process session covers it just as well.
;
; "--solver test" forces the mock solver regardless of which solver FileTests' own
; (solver, file) parameterization picked: this is a jSMTLIB parser-level characterization
; (see ok_reservedWordsRelaxCommand.tst's own note on why a real solver isn't relevant here).
(set-logic QF_UF)
(declare-const ! Bool)
(declare-const _ Bool)
(declare-const as Bool)
(declare-const DECIMAL Bool)
(declare-const exists Bool)
(declare-const forall Bool)
(declare-const let Bool)
(declare-const match Bool)
(declare-const NUMERAL Bool)
(declare-const par Bool)
(declare-const STRING Bool)
