# Solver behavior tests

Scripts here talk directly to solver binaries (piping SMT-LIB text to their
stdin/stdout), bypassing jSMTLIB entirely. They exist because the behaviors
they check either can't be observed through jSMTLIB at all (jSMTLIB
normalizes or intercepts them client-side) or need to run identically against
every installed version of a solver family, which a single `.tst` golden file
can't express.

Each script auto-discovers every `z3-*`/`cvc5-*`/`yices2-*`/`smtinterpol-*.jar`
executable under `$SMT_SOLVER_DIR` and runs the same checks against each, so a
newly-installed solver version is covered automatically with no script
changes needed. (`solver-output-channel.scr` predates the yices2/SMTInterpol
support added for the other two and still only covers z3/cvc5 — see its own
section below.)

`solver-output-channel.scr` and `print-success.scr` are marked `.skip`
(portability: some of what they report — e.g. per-version informational
output, exact platform behavior — depends on which solver versions happen to
be installed locally) — run them directly for an up-to-date assessment:

```
bash runscript scripts/solverBehavior/solver-output-channel.scr
bash runscript scripts/solverBehavior/print-success.scr
```

(`runscript` respects the `.skip` marker; invoke the `.scr` file with plain
`bash` instead to bypass it, as both commands above do implicitly through
the direct-run examples in each script's own header.)

`all-statistics.scr` is **not** skipped: every check it makes is a fixed
structural PASS/FAIL (never a raw memory/timing value), so it runs as part
of the normal `./runscripts`/JUnit suite like any other `.scr` test — its
`.out`/`.err`/`.cmb` goldens list whichever solvers happen to be installed
locally, so they need regenerating (delete and rerun) if the local solver
set changes.

## solver-output-channel.scr

Checks `:regular-output-channel`/`:diagnostic-output-channel` redirection and
restore, plus filesystem behavior (does redirecting to a missing file create
it? a missing directory? what happens if the target already has content?).

**Current assessment** (all z3 versions 4.3.1–4.16.0, cvc5-1.3.2 — re-verified
this session): all PASS on the redirect/restore correctness check. Documented,
non-bug differences: z3 **appends** to a pre-existing redirect target, cvc5
**truncates** it — the standard doesn't mandate either, so this is recorded as
an intentional per-solver difference, not a compliance issue. Neither solver
creates a missing parent directory for the redirect target (both error
instead) — the same for both, also fine either way per spec.

## print-success.scr

Checks three things about the `:print-success` option, none of which a
`.tst` file can observe (jSMTLIB handles `:print-success` entirely
client-side and always leaves the real solver pinned at `:print-success
true` at the wire level — see `AbstractSolver.java`'s `checkPrintSuccess` doc
comment):

1. **Default value under SMT-LIB 2.5/2.6/2.7** (each declared via an initial
   `(set-info :smt-lib-version X)`, per the standard's own requirement that
   it be the first command).
2. **Success-emission mechanics**: once `:print-success` is set, `success`
   must be emitted for every purely-acknowledging command (`set-logic`,
   `declare-fun`, `assert`, `set-option`, and — easy to get wrong — `exit`
   itself), must be suppressed for those same commands when off, and a
   substantive answer (`check-sat`) must never be suppressed either way.

### What the reference documents actually say, release by release

Pulled directly from every PDF listed on the
[official version history](https://smt-lib.org/language.shtml)
(`pdftotext` extraction, `:print-success` entry, verbatim):

| Version | Release date | `:print-success` default |
|---|---|---|
| 2.5 | 2015-06-28 (only release) | **true** |
| 2.6 | 2017-07-18 | **true** |
| 2.6 | 2021-04-02 | **true** |
| 2.6 | 2021-05-12 | **true** |
| 2.6 | 2024-09-20 ("Latest") | **false** |
| 2.7 | 2025-02-05 through 2026-03-27 (all 4 releases) | **false** |

So the transition is precise: **every 2.6 release for seven years (2017–2021)
said `true`; only the final 2.6 release, three years later in 2024, flipped
it to `false`** — and the description text changed to match ("setting to
`false` suppresses success" became "setting to `true` prints success", a full
inversion, not just the default flag). 2.7 kept the 2024-era 2.6 wording
unchanged. This confirms exactly what you described: early 2.6 = true, final
official 2.6 = false, matching 2.7.

A version number like "2.6" names one evolving document, not four permanent
ones — the 2017/2021/2021 releases were superseded by the 2024 release, not
preserved as separate specs. So the test below judges a declared `2.6`
against its **current, authoritative** document (the 2024-09-20 release,
`false`), not against superseded earlier drafts of the same number.

### Current assessment

(all z3 versions 4.3.1–4.16.0, cvc5-1.3.2, both yices2 versions, SMTInterpol
2.5 — 13 solvers total, checked this session; `##EXITCODE 1` reflects a
confirmed real failure, not a script bug):

| Family | @2.5 (want `true`) | @2.6 (want `false`) | @2.7 (want `false`) | exit acked? | success-emission |
|---|---|---|---|---|---|
| z3 (all 9 versions) | FAIL (`false`) | PASS | PASS | yes | PASS |
| cvc5-1.3.2 | FAIL (`false`) | PASS | PASS | yes | PASS |
| yices2 (both versions) | FAIL (`false`) | PASS | PASS | yes | PASS |
| SMTInterpol 2.5 | PASS | FAIL (`true`) | FAIL (`true`) | **no** | **FAIL** |

None of the 13 tested solvers actually implement the version-conditioned
default — each just hardcodes one fixed value regardless of which SMT-LIB
version is declared (confirmed directly: for every solver, the raw responses
to explicit `2.5`/`2.6`/`2.7` declarations are identical). z3, cvc5, and
yices2 (12 of 13) hardcode `false` — correct against every currently
authoritative document except 2.5. SMTInterpol alone hardcodes `true` —
correct only against 2.5, and against the three now-superseded early 2.6
drafts, but not against anything currently authoritative beyond 2.5 itself.

**SMTInterpol's own target is 2.5, not the current standard.** Its own
project documentation
([news page](https://ultimate.informatik.uni-freiburg.de/smtinterpol/news.html))
states that the SMTInterpol-2.5 release supports SMT-LIB 2.5, and its jSMTLIB
adapter code (`Solver_smtinterpol.java`'s doc comment) independently
describes it as "empirically fully SMT-LIB compliant: `:print-success`
already defaults to true" — a claim made by that solver's own jSMTLIB
integrator, unprompted by this investigation. Read against SMTInterpol's own
stated target (2.5, where `true` is and always was correct), its behavior is
exactly right; its FAIL rows above only mean it hasn't adopted anything from
2.6's 2024 revision onward, which it never claimed to.

z3/cvc5/yices2, by contrast, give no indication of targeting a specific
SMT-LIB version for this option — they simply always answer with whatever is
correct for the *current* standard, silently, regardless of what version a
script declares. That's arguably a more defensible stance for a solver that
doesn't want to carry old per-version option-default branches forward
indefinitely, but it does mean none of them can correctly run a 2.5-targeted
script relying on the then-documented `true` default.

**Bonus finding**: SMTInterpol also fails the success-emission mechanics
check on a different axis — it does not print `success` for `exit` at all
(the other 12 solvers all do). Confirmed via direct line-count comparison,
not just the diff-based check: 6 response lines where 7 were expected, exit
producing none.

## all-statistics.scr

Checks `(get-info :all-statistics)` for z3, cvc5, yices2, and SMTInterpol,
on two axes: response **shape** and the standard's explicit **mode**
requirement. This was previously checked only for cvc5-1.3.2 (the
now-removed `scripts/getInfo-allStatistics-cvc5.scr`); generalized here
across all four families and moved alongside the other raw-solver checks.
Unlike the other two scripts in this folder, it is **not** `.skip`ed, since
every assertion it makes is a fixed PASS/FAIL classification, never a raw
value comparison.

**Response shape.** `:all-statistics` is a generic/vendor-specific info
request (see the comment in `tests/getInfo/err_getInfo2_allStatistics.tst`):
the standard requires only that the response be a list of attribute-value
pairs, not any particular shape or content, and every solver's response
embeds live, non-deterministic values (timings, memory/allocation counts,
term/type counts) that can never be matched against a fixed golden — the
check only verifies the response opens with `(`, contains at least one
`:keyword` attribute name, and has balanced parentheses. Two response shapes
are both seen in practice and both accepted, since the standard doesn't
mandate one over the other:

- z3 and yices2 return a **flat attribute-list** directly, e.g.
  `(:max-memory 0.29 :memory 0.29 :num-allocs 633 :rlimit-count 1)` — no
  `:all-statistics` wrapper key.
- cvc5 and SMTInterpol **wrap** everything under a single `:all-statistics`
  key whose value is itself a nested list, e.g.
  `(:all-statistics ((:Core (...)) (:CC (...))))`.

All 13 solvers checked PASS the shape check in both sat and unsat mode
(see below).

**Mode requirement.** The SMT-LIB 2.7 reference (§4.1.8) states:
`:all-statistics ... mode: sat, unsat` — "Executions of get-info with
:all-statistics are allowed only when the solver is in sat or unsat mode."
Combined with the general requirement in §4.1.1, "The solver must respond
with an error when given a command not permitted in the current mode," a
compliant solver **must** reply with `(error ...)` — not statistics data —
if `:all-statistics` is requested before any `check-sat` (start/assert
mode). Three single-session runs per solver test this:

- **A** — before any `check-sat` (assert mode): must get `(error ...)`.
- **B** — after a `check-sat` that reports `sat` (sat mode): must get
  well-formed data.
- **C** — after a `check-sat` that reports `unsat` (unsat mode): must get
  well-formed data.

**Current assessment** (all 9 z3 versions, cvc5-1.3.2, both yices2 versions,
SMTInterpol 2.5 — 13 solvers total; `##EXITCODE 1` reflects a confirmed real
failure, not a script bug):

| Family | Run A (want error) | Run B (sat mode) | Run C (unsat mode) |
|---|---|---|---|
| z3 (all 9 versions) | **FAIL** (well-formed data instead) | PASS | PASS |
| cvc5-1.3.2 | **FAIL** (well-formed data instead) | PASS | PASS |
| yices2 (both versions) | **FAIL** (well-formed data instead) | PASS | PASS |
| SMTInterpol 2.5 | **FAIL** (well-formed data instead) | PASS | PASS |

**Every one of the 13 solvers checked violates the mode requirement**: none
of them reject a pre-`check-sat` `:all-statistics` request with an error —
all of them silently compute and return statistics anyway (memory/allocation
counts for z3, term/type counts for yices2, full solver-internal stat trees
for cvc5/SMTInterpol), even though nothing has been solved yet and the
standard says this is not a permitted mode for the command. Runs B and C
(the two modes the standard actually allows) pass cleanly for all 13 — the
statistics content differs materially before vs. after `check-sat` (e.g. z3's
`:num-allocs`/`:rlimit-count`, cvc5's timing fields), so this isn't a case of
solvers ignoring the state machine entirely — they just don't enforce the
precondition on this particular command.
