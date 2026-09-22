; A second set-logic command without --relax must be rejected outright -- SMT-LIB
; permits only one set-logic per session. Closes a real coverage gap found while
; auditing Solver_simplify.java: its setLogicLocal() has a whole "logicSet != null"
; branch (both the non-relax error here and the --relax reset path in
; ok_setLogicRelax.tst) that no test in this suite exercised at all -- the closest
; existing test, err_setLogic.tst, issues several set-logic commands but each one is
; independently malformed, so logicSet is never actually set by any of them and none
; reach this check.
;
; Not simplify-only, but not uniform either: z3 and the mock "test" solver share this
; exact jSMTLIB-generated wording (both have their own client-side "already set" gate,
; the same shape as Simplify's), while cvc5/yices2/smtinterpol have no such gate at all
; -- they forward every set-logic straight to their own process, which then separately
; gives its own native rejection wording. Confirmed empirically against real local
; binaries of all of these except simplify/bitwuzla (unavailable on this machine); the
; bare golden below holds the jSMTLIB-generated wording (matching test/z3), with
; solver-specific overrides for cvc5/yices2/smtinterpol's own native text. Simplify's
; setLogicLocal() is a direct transplant of this same check (see its own class-doc), so
; it should match the bare golden too, but that is reasoned from reading the code, not
; independently confirmed against a real Simplify process.
(set-logic QF_UF)
(declare-fun x () Bool)
(set-logic QF_UF)
