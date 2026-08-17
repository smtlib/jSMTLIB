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

## Conclusion

The per-command overhead found in `raw-vs-jsmtlib` is, to a close
approximation, entirely explained by `SolverProcess.errorSettleMillis`.
It is a deliberate, recently-added correctness fix, not legacy cruft,
and there is no value of it that is simultaneously fast and fully safe
against arbitrary stderr timing — only a trade between the two. Given
that OpenJML's real workload (long, mostly-error-free scripts) pays this
cost thousands of times per invocation, lowering it is a genuinely
promising lever for proof turnaround time, but it is a decision to make
deliberately, with the tradeoff above in view — not something this
experiment changes on its own.

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
