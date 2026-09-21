; OPTIONS: --relax --solver test
; Issue #33: Log.logOut(String) used to add no line termination (byte-for-byte identical to
; logOutNoln(String)), so the non-standard :what command's one-logOut-call-per-symbol-table-
; entry loop ran every entry together on a single unbroken line. Fixed by having logOut(String)
; add a line termination, matching its sibling overloads' existing convention.
;
; (what) with no arguments lists every defined id -- with more than one entry, the bug would
; show up as everything landing on one line instead of one entry per line.
;
; "--solver test" forces the mock solver regardless of which solver FileTests' own
; (solver, file) parameterization picked for this run: (what) is a Solver_test-only
; pseudo-command (see AbstractSolver's own rejection message for every real adapter), so
; there is no real-solver behavior to characterize here, only Solver_test's own.
(set-logic QF_UF)
(declare-const a Bool)
(declare-const b Bool)
(what)
