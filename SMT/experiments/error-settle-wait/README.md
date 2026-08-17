# Per-command overhead: `errorSettleMillis`

## Research question

The `raw-vs-jsmtlib` experiment found that jSMTLIB imposes a large,
roughly constant ~280-330ms of overhead per solve, independent of
solver and of proof difficulty. jSMTLIB dispatches SMT-LIB commands to
the solver one at a time, writing each and waiting for its response
before sending the next — so a natural next question is whether that
overhead is really a *per-solve* constant, or a *per-command* cost that
happens to look constant because the earlier scripts all had a similar,
small number of commands per solve (7-9). This experiment tests that
directly, and tracks down the mechanism responsible.

## Method

`generate_percommand.sh K N outputFile` builds a script of `N`
iterations joined by `(reset)`, where each iteration is just `K` trivial
filler `declare-fun`s followed by `(check-sat)` — no assertions, so
solving is trivially fast regardless of `K`. This isolates the marginal
cost of sending more individual commands from any actual solving cost.

`run_percommand.sh N solver [K1 K2 ...]` runs that script, for each `K`,
both directly against the raw solver and through the jSMTLIB CLI (same
launch-flag-matching and `$EPOCHREALTIME`-based timing as
`raw-vs-jsmtlib`), and reports `jsmtlib_per_iter_ms` alongside the
implied per-command overhead.

## Results

N=20, z3-4.16.0, against the committed build (`errorSettleMillis = 20`):

| K | commands/iter | jSMTLIB overhead/iter | overhead/command |
|---:|---:|---:|---:|
| 0 | 2 | 79 ms | 39.7 ms |
| 10 | 12 | 309 ms | 25.8 ms |
| 25 | 27 | 662 ms | 24.5 ms |
| 50 | 52 | 1237 ms | 23.8 ms |
| 100 | 102 | 2389 ms | 23.4 ms |

The overhead is essentially perfectly linear in command count — the
slope between every consecutive pair of points is ~23ms/command (K=0→10:
23.0, K=10→25: 23.5, K=25→50: 23.0, K=50→100: 23.0) — confirming this is
a genuine per-command cost, not a per-solve constant. (default.smt2 vs.
bv16.smt2 in `raw-vs-jsmtlib`, at 7 vs. 8 commands respectively, already
hinted at this: the ~12.5% difference in command count roughly matched
the ~8-13% difference in measured overhead.)

## Root cause

`SolverProcess.java`:

```java
public long errorSettleMillis = 20;
```

`listen()` calls `errorOut.drain(errorSettleMillis)` after *every*
command's stdout end-marker is recognized. `drain()`'s own comment
explains why: recognizing the end marker on stdout says nothing about
whether the independently-scheduled stderr-reading thread has finished
reading whatever error text the solver wrote alongside it, so `drain()`
polls its queue with `settleMillis` as the timeout for the *first*
chunk, not just for stragglers afterward — paid in full even when a
command produces no error text at all, which is nearly always.

**Confirmed empirically**: temporarily changed `errorSettleMillis` from
`20` to `1`, rebuilt, and reran the same K-sweep:

| K | commands/iter | jSMTLIB overhead/iter | overhead/command |
|---:|---:|---:|---:|
| 0 | 2 | 17 ms | 8.3 ms |
| 10 | 12 | 30 ms | 2.5 ms |
| 25 | 27 | 54 ms | 2.0 ms |
| 50 | 52 | 83 ms | 1.6 ms |
| 100 | 102 | 157 ms | 1.5 ms |

Per-command overhead collapsed from ~23ms to ~1.5-2.5ms — nearly all of
the cost measured above is this one field. The change was reverted and
`jSMTLIB.jar` rebuilt back to the committed state immediately after;
nothing was left modified.

## History: what was it before?

`errorSettleMillis` was introduced in commit `0e15054e` ("Add
configurable charset to SolverProcess and rewrite gobbler threading",
2026-08-15), a rewrite of the stdout/stderr-reading machinery earlier in
this same week. Before that commit, there was no deliberate settle-wait
at all: stderr was fetched with a non-blocking `errorOut.getString()`
immediately after stdout completed, and the code's own comment at the
time candidly acknowledged the tradeoff: *"errorOut is set up to not
block -- presuming error output is ready if standard out has completed,
since there is no indication when the error output is completed."*

In other words, this went from effectively **0ms** (fast, but racy —
capturing whatever stderr text happened to already be queued, no more)
to **20ms** (the rewrite's deliberate fix for that race) very recently,
not a long-standing constant. The fix was for a real, previously
observed bug: `StreamGobbler.drain()`'s own comment describes exactly
what went wrong under the old approach — *"an entire command's
error-and-echo block silently missing from a script's output, not
merely truncated at a boundary."* So `errorSettleMillis = 20` is not
arbitrary cruft; it is a considered fix for a real correctness problem,
and the ~23ms/command cost measured here is the price of that fix, not
an oversight.

## Why this isn't a simple "just lower the number"

Two things make this more than a tuning knob:

**Stderr timing is fundamentally unbounded.** A solver can write
diagnostic or error output to stderr at any time relative to when it
finishes a command's stdout response — there is no OS-level signal
tying the two together (this is exactly what `drain()`'s comment says).
`errorSettleMillis` is a heuristic grace period, not a guarantee at any
value: shrinking it reduces the window in which a legitimately slow
stderr write gets missed, but does not eliminate it. Lowering it is a
real trade of correctness margin for speed, not a free win.

**Real usage amplifies this differently than these experiments do.**
OpenJML's actual use of jSMTLIB sends one script that can be a few
thousand commands long — declarations, definitions, and assertions —
ending in a single `(check-sat)`. Such a script is correct by
construction except when there is an actual bug being hunted, so the
overwhelming majority of those thousands of commands produce no error
output at all. At `errorSettleMillis = 20`, each one still pays the
full 20ms wait: a 3,000-command script pays roughly 60 seconds of pure
dead time before ever reaching the `check-sat` that does the real work,
almost all of it waiting for error text that was never coming. That is
likely to dwarf actual solve time for many such scripts, which is a
different and larger-scale version of the effect measured here at
K ≤ 100 — worth keeping in mind since it means the real-world payoff of
addressing this is plausibly much bigger than the experiment's own
numbers suggest, not smaller.

## What do real solvers actually put on stderr?

The risk `errorSettleMillis` guards against is only worth its cost if
solvers actually do write meaningful diagnostic text to stderr with
unpredictable timing. That's testable directly: feed each raw solver
(same launch flags jSMTLIB uses) a script and inspect its *actual*
OS-level stderr, bypassing jSMTLIB's own output handling entirely.

Two scenarios per solver: a clean script (declare, assert, check-sat,
all succeeding), and an error-provoking one (`(get-proof)` without
`:produce-proofs`, followed by a syntactically-unrecognizable command).

| solver | clean script stderr | error script stderr |
|---|---|---|
| z3-4.16.0 | empty | one line: `; this-is-not-a-command line: 6 position: 22` |
| cvc5-1.3.2 | empty | empty — both errors came back as `(error "...")` on **stdout** |
| yices2-2.7.0 | empty | empty — both errors came back as `(error "...")` on **stdout** |
| smtinterpol-2.5 | empty | empty — both errors came back as `(error "...")` on **stdout** |

Three of the four solvers currently in use write **nothing** to stderr
in either scenario — every error, including `get-proof`'s, comes back as
a proper SMT-LIB `(error "...")` response on stdout, which is what the
spec calls for and is unaffected by `errorSettleMillis` (that field only
guards the *stderr* pipe). z3 is the only one that used stderr at all,
and only for a command it couldn't parse as SMT-LIB syntax at all — not
for an ordinary semantic error like an unsupported command with
well-formed syntax — and even then it was one short comment line, not
the kind of large or delayed diagnostic block the 20ms grace period was
designed to catch.

This also answers a question raised in review: the caret-annotated
`(get-proof)` / `^^^^^^^^^^^` block seen in `SMTTests`' own golden files
for yices2 (`tests/getProof/ok_getProof.tst.err.yices2`) is **not**
anything the yices2 process itself writes to stderr — confirmed above,
its raw stderr for that exact scenario is empty. That text is
synthesized entirely by jSMTLIB itself: `Log.logError(IError)` (in
`SMT/src/org/smtlib/Log.java`) writes a source-line-and-caret
`locationIndication(...)` to `Log.diag` (which `SMTTests`' harness
happens to capture into the same `.err` golden) whenever a response
parses as an error with position info attached — using jSMTLIB's own
record of where in the *original script* the offending command was, not
anything relayed from the solver's stderr pipe. So `.err` golden files
in this repo are a mix of two unrelated things: genuine captured solver
stderr (via `SolverProcess.errorOut`, the thing `errorSettleMillis`
waits on) and jSMTLIB's own synthesized diagnostics (via `Log.diag`,
synchronous, not subject to any IPC race at all). Only the former is
relevant to this experiment; based on the table above, it's nearly
always empty for the solvers actually in use.

(Not exhaustively tested: solver behavior under resource exhaustion,
memory pressure, or other stress conditions might produce stderr
warnings this quick pass didn't provoke. The scope here is jSMTLIB's
actual launch configuration under normal successful-and-erroring
scripts, which is the overwhelmingly common case for OpenJML's
correct-by-construction usage.)

## Conclusion and recommendation

The per-command overhead found in `raw-vs-jsmtlib` is, to a close
approximation, entirely explained by `SolverProcess.errorSettleMillis`.
It is a deliberate, recently-added correctness fix, not legacy cruft —
but the risk it guards against turns out to be rare in practice for the
solvers actually in use: three of four never write to stderr at all
under normal or erroring conditions, and the fourth (z3) only does so
for unparseable input, briefly and (in this synchronous test) promptly.
The actual error *information* is essentially always delivered reliably
regardless, via the standard `(error "...")` response on stdout — the
`.err`-golden caret text some tests exercise is a jSMTLIB-side
convenience for showing script context, not the primary carrier of the
error, and isn't at risk from a shorter stderr wait.

**Recommendation: drop `errorSettleMillis` from 20ms to something in
the 1-2ms range**, not all the way to 0. A small nonzero value keeps a
token grace period for the already-rare case (mainly z3's parse-error
comments) without meaningfully changing the economics: at 1ms, the
measured per-command overhead was already down to ~1.5-2.5ms, next to
~23ms at the current default — an order of magnitude improvement — and
for OpenJML's few-thousand-command, correct-by-construction scripts
where the current setting can plausibly cost tens of seconds of pure
waiting before the real solving even starts, this is likely to matter a
lot more in practice than the numbers measured directly in this
experiment. It does not eliminate the theoretical race `errorSettleMillis`
exists for — no fixed value does, since stderr timing has no OS-level
guarantee — but the empirical evidence above suggests that risk is
small and, when it does bite, costs a supplementary diagnostic line, not
the underlying error result.

## Reproducing

```
cd SMT/experiments/error-settle-wait
./run_percommand.sh 20 z3-4.16.0 0 10 25 50 100
```

Requires `SMT_SOLVER_DIR` to be set (or resolvable via
`SMTTests/setup`) and `SMT/jSMTLIB.jar` already built. To reproduce the
`errorSettleMillis = 1` comparison, edit the field in
`SMT/src/org/smtlib/SolverProcess.java`, run `SMT/buildRelease`, rerun,
then revert and rebuild again.
