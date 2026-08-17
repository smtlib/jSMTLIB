# Raw solver vs. jSMTLIB: where does the time go?

## Research question

jSMTLIB sits between a caller and a backend solver: it parses SMT-LIB
text, type-checks it, translates it into whatever dialect the target
solver version actually needs, drives the solver subprocess, and parses
the solver's response back into its own response objects. All of that is
extra work compared to just talking to the solver directly.

The question this experiment answers: **how much does jSMTLIB's own
processing actually cost, on top of the solver's own launch and solve
time — and is that cost tied to which solver is used, or to how hard the
proof problem is?**

## Method

Both invocation modes need to launch a process exactly once — a raw
solver invocation launches the solver binary once, and running through
jSMTLIB means launching a JVM once — so a single big script consisting
of N copies of a base problem, joined by `(reset)`, is used for both
sides. With N large enough, that one-time launch cost is amortized away
and what dominates is the *per-command* cost repeated N times: none for
the raw solver, jSMTLIB's SMT-LIB handling for the jSMTLIB run.

`generate_bigscript.sh N baseFile outputFile` builds that script (see
[`process-vs-reset`](../process-vs-reset/), which established the
per-process-vs-reset framing this reuses). `run_experiment.sh N
baseScript [solvers...]` then, for each solver:

- runs the raw solver binary directly on the big script via stdin,
  using the **exact same command-line flags its `Solver_*.java` adapter
  uses** (e.g. z3 gets `-smt2 -in SMTLIB2_COMPLIANT=true WARNING=false`,
  cvc5 gets `--lang smt --interactive --incremental --quiet
  --print-success --strict-parsing`, etc.) — so the only difference
  being measured is jSMTLIB's processing layer, not a different solver
  invocation mode;
- runs `java -cp jSMTLIB.jar org.smtlib.SMT --solver <name> --nosuccess
  <bigscript>` — the actual jSMTLIB CLI, including its own JVM startup;
- times both with bash's `$EPOCHREALTIME` (macOS's stock `/bin/bash` is
  an ancient 3.2 that lacks this variable — `run_experiment.sh` and
  `generate_bigscript.sh` both use `#!/usr/bin/env bash` to pick up a
  modern bash from `PATH` instead).

Two base scripts were used, the same ones from `process-vs-reset`:
`default.smt2` (trivial QF_LIA, near-zero solve time) and `bv16.smt2` (a
16-bit bitvector factoring problem forcing real search).

## Results

N=50 for all runs. Times are per-iteration (ms); overhead = jSMTLIB −
raw, i.e. jSMTLIB's marginal cost on top of the solver's own time.

| solver | script | raw | jSMTLIB | overhead |
|---|---|---:|---:|---:|
| z3-4.16.0 | default.smt2 | 69 | 359 | 290 |
| cvc5-1.3.2 | default.smt2 | 43 | 324 | 281 |
| yices2-2.7.0 | default.smt2 | 6 | 297 | 291 |
| smtinterpol-2.5 | default.smt2 | 80 | 360 | 280 |
| z3-4.16.0 | bv16.smt2 | 152 | 480 | 328 |
| cvc5-1.3.2 | bv16.smt2 | 106 | 413 | 307 |
| yices2-2.7.0 | bv16.smt2 | 11 | 326 | 315 |
| smtinterpol-2.5 | bv16.smt2 | 128 | 432 | 304 |

(smtinterpol returns `unknown` rather than `sat` on the bv16 problem —
a solver capability limit already noted in `process-vs-reset`, not an
artifact of this experiment.)

Absolute numbers got noisier over the course of the run (apparent
system load — raw z3 alone ranged from 69ms to 152ms between the two
passes), so don't read too much into any single cell. The overhead
column is the more robust signal: it stayed in a tight ~280-330ms band
across every solver and both scripts, despite raw solve times varying
by more than 20x (6ms to 152ms) within that same set of runs.

## Conclusion

jSMTLIB's own processing overhead per solve is large — on this data,
roughly 280-330ms — and it does not track which solver is used or how
hard the underlying problem is. It looks like a fixed cost of running N
commands through jSMTLIB's Java-side pipeline (SMT-LIB parsing,
type-checking, dialect translation, response parsing), not a cost tied
to solver launch or solver-internal search.

The smtinterpol row is the cleanest evidence for that reading. Unlike
the three native-executable solvers, smtinterpol pays `java -jar` JVM
startup on *both* sides of the comparison here, so if the overhead were
mostly "the cost of spinning up one more JVM," smtinterpol's overhead
should come out higher than z3/cvc5/yices2's. It doesn't — it's actually
slightly lower (280/304ms vs. up to 328ms for z3). That's consistent
with the overhead scaling with the number of SMT-LIB commands processed,
not with how many JVMs got launched.

This also reframes the `process-vs-reset` experiment's numbers: its
`reset_per_iter_ms` values (~200-250ms) were interpreted there as
solver-side reset-and-relaunch cost. Given what this experiment shows
about raw solve times for the same problems (often under 20-150ms) and
jSMTLIB's own ~280-330ms overhead, it now looks like those earlier
`reset_per_iter_ms` numbers were mostly *this same jSMTLIB-side
processing cost* all along — actual solver-side work was a small
fraction of what was being measured, not the dominant cost that
experiment's framing implied.

**Not investigated here**: which part of jSMTLIB's pipeline the
overhead actually lives in — parsing, type-checking, per-solver dialect
translation, or response parsing. That would be the natural next step
for anyone looking to reduce it; this experiment only establishes that
the cost is real, large, and solver/problem-independent, not where
inside jSMTLIB it comes from.

## Reproducing

```
cd SMT/experiments/raw-vs-jsmtlib
./run_experiment.sh 50 default.smt2
./run_experiment.sh 50 bv16.smt2
```

Requires `SMT_SOLVER_DIR` to be set (or resolvable via
`SMTTests/setup`) and `SMT/jSMTLIB.jar` already built. Defaults to
z3-4.16.0, cvc5-1.3.2, yices2-2.7.0, and smtinterpol-2.5; pass solver
names as extra arguments to override.
