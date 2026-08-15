
This file summarizes teh status of test results.

Remaining skips: 45 files, 5 categories

OUTPUT FILES MARKED SKIP

1. ARM64-only z3-4.3.1 bugs — 15 files (6 distinct test files, z3+z3_4_3 × linux-arm64/macos-arm64)
No ARM64 hardware to verify these on, so they're unconfirmed-but-plausible:
- ok_array2, ok_ALL2_logic_8, ok_globaldeclarations4 — "returns wrong sat/unsat on ARM64" (a soundness bug, not a hang — worth eventually converting to .bad goldens if someone with ARM64 access can confirm the exact wrong answer is deterministic)
- ok_getAssertions2 — "returns incomplete get-assertions output on ARM64"
- err_getInfo2, err_setInfo3 — "hangs on getInfo queries on ARM64"

2. cvc5-1.3.2 architectural limits — 4 files
- err_getInfo2, err_getInfo2_allStatistics — :all-statistics embeds non-deterministic timing values scattered through a nested structure (not a single filterable line), so no stable golden is possible
- ok_regularOutput, ok_setRequiredOptions — cvc5 genuinely redirects its output stream to the named file when asked (correct behavior), which desyncs jSMTLIB's synchronous pipe protocol for the next response — a real protocol blind spot, not a bug

3. yices2 (bare name — applies to yices2-2.6.5/2.7.0 too via family fallback) — 12 files, all quantTests/
"yices2 does not implement quantifiers" / "yices2 crashes" / "yices2 has a bug here (Feb 2014)". These predate this session's yices2-2.6.5/2.7.0 work — I spot-checked 4 of them earlier and modern yices2 doesn't hang or crash on them, it cleanly rejects the logic ("logic AUFLIA is not supported") and cascades clean errors. So this content is real and observable, just currently hidden — flagged in my original assessment as likely-stale but not yet acted on (you didn't include this category in the "fix" request).

4. simplify — 12 files, quantTests/ + satChecks/
Untouched per your instruction — you said it's a real binary you haven't re-engaged yet.

5. Genuine, individually-confirmed bugs — 2 files
- err_declareSortParameter_dup.tst.skip.smtinterpol — SMTInterpol hangs (no response ever sent) when the same malformed command is sent twice in a row interactively; confirmed via direct piping, batch/file input handles it fine.
- err_tokens.tst.skip.z3_4_3 — z3-4.3.1 deadlocks: an invalid string escape (\d) makes it misparse the closing quote as escaped, consuming all subsequent input; jSMTLIB keeps sending commands into the void.

Categories 1–2 are legitimate as-is. Category 3 (yices2) is the one open item from my original assessment I haven't remediated — want me to do that next, same treatment as the z3_4_3/cvc5 work?

SCRIPT FILES

Of the 48 .scr files under SMTTests/scripts/, most use jSMTLIB's built-in pure-Java test solver (either --solver test explicitly, or no --solver flag at all — the default in jsmtlib.properties falls back to test). Only these actually depend on a real external solver binary:

Genuinely need a working external solver to pass:

┌────────────────────────────────┬────────────────────┬───────────────────────────────────────────────────────────┐
│             Script             │       Solver       │                       How resolved                        │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ batch-smt.scr                  │ z3-4.3.x           │ via SMT_SOLVER_DIR/PATH                                   │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ path-res-absolute.scr          │ z3-4.3.1           │ absolute path                                             │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ path-res-path.scr              │ z3-4.3.1           │ via PATH                                                  │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ path-res-solverdir.scr         │ z3-4.3.1           │ via SMT_SOLVER_DIR                                        │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ zapi.scr                       │ z3-4.3.1           │ hardcoded in APIExample.java (Solver_z3_4_3), not visible │
│                                │                    │  in the .scr text itself                                  │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ solver-output-channel.scr      │ every z3-*/cvc5-*  │ invokes solvers directly, bypassing jSMTLIB; gracefully   │
│                                │ found              │ SKIPs (exit 0) if none found                              │
├────────────────────────────────┼────────────────────┼───────────────────────────────────────────────────────────┤
│ getInfo-allStatistics-cvc5.scr │ cvc5-1.3.2         │ gracefully SKIPs (exit 77) if absent                      │
│                                │ specifically       │                                                           │
└────────────────────────────────┴────────────────────┴───────────────────────────────────────────────────────────┘

Reference a solver but only to exercise jSMTLIB's own error-handling — don't actually need a working solver, expect EXITCODE 1:
- batch-smt2.scr, batch-smt3.scr, batch-smt4.scr (unconfigured/bogus simplify solver — batch-smt3.scr even has a comment noting it's a stale hardcoded Windows path)
- path-res-error.scr (deliberately nonexistent exec)

Everything else (31 files) runs entirely against the built-in test solver, no external binary needed.

