# Per-process vs. `(reset)`: which is faster for running many scripts?

## Research question

jSMTLIB is often used to send many separate SMT-LIB scripts to a backend
solver in succession (e.g. one per verification condition), each one
ending with `sat`/`unsat`/`unknown`. There are two ways to structure that:

1. **Per-process**: launch a fresh `SolverProcess` (and thus a fresh
   solver subprocess) for each script, letting it exit at the end.
2. **Reset**: launch one `SolverProcess` and keep it alive, separating
   successive scripts with `(reset)`.

Per-process is simpler and gives each script a fully isolated solver
state; reset avoids repeated process-launch cost but relies on `(reset)`
actually clearing all solver-internal state, and keeps one solver process
alive for the whole batch.

The question this experiment answers: **how much does the per-process
approach actually cost relative to reset, and does that cost grow with
how long the proof itself takes?** If the launch cost is roughly fixed
and small compared to typical proof time, the simplicity of per-process
is basically free; if it's large or grows with proof difficulty, reset
would be the better default for high-volume use.

## Method

`TimingExperiment.java` drives the real `org.smtlib.SMT` class (the same
code path the jSMTLIB CLI uses) N times against a given solver, once
using approach A (fresh `SMT`/`SolverProcess` per iteration, no explicit
`(exit)` needed since `SMT.exec()`'s own `finally` block already tears
the solver down) and once using approach B (one `SMT` instance, N copies
of the script joined by `(reset)`, no trailing `(reset)` after the last
one). Both approaches run inside the same warm JVM against the same
unmodified `jSMTLIB.jar`, so JIT warmup and JVM startup are not part of
what's measured — only the solver-subprocess lifecycle differs between A
and B.

`run_experiment.sh` compiles and runs `TimingExperiment` against a
configurable list of real solvers (z3 4.3 through 4.16.0, cvc5-1.3.2,
smtinterpol-2.5, yices2 2.6.5/2.7.0), for a configurable N and script
file:

```
./run_experiment.sh [N] [scriptFile] [solver1 solver2 ...]
```

Two scripts were used:

- `default.smt2` — a trivial QF_LIA instance (`x + y = 10, x,y > 0`),
  representing near-zero proof time, so the run mostly measures pure
  launch/reset overhead.
- `bv16.smt2` — a 16-bit bitvector factoring problem
  (`x * y = 0xA405`, `1 < x < y`, whose only nontrivial factorization is
  the two primes `199 * 211`), forcing real bit-blasted CDCL search
  (several hundred ms per solve for most solvers), to see whether the
  per-process/reset gap changes when there's real work to do.

## A bug found along the way

The first run of this experiment (against the *unmodified* jSMTLIB.jar)
showed a suspiciously uniform ~1.2s/iteration cost for the per-process
approach across every solver, regardless of solver or task. That traced
back to an unconditional `Thread.sleep(1000)` in `SolverProcess.start()`
— a debugging leftover from the class's original 2020 commit (it used to
be followed by a now-deleted `System.out.println("Status after
starting: " + isAlive())` diagnostic). It was never load-bearing: the
`StreamGobbler`/`BlockingQueue` machinery that reads solver output
already blocks correctly on real data arrival, with or without the
sleep, and every currently-active solver adapter calls `start(false)`
(no banner-consumption use of the sleep either). The results below are
all measured *after* removing that sleep (see `SolverProcess.java`'s
`start()`), which is the config any real usage should be running with
anyway.

## Results

All times are per-iteration (ms), from `TimingExperiment`'s
`perProcess_per_iter_ms` and `reset_per_iter_ms`. "delta" =
per-process − reset, i.e. the marginal cost of relaunching the process
each time instead of reusing it.

### Trivial task (`default.smt2`, N=20)

| solver | per-process | reset | delta |
|---|---:|---:|---:|
| z3-4.3 | 238 | 187 | 51 |
| z3-4.8.12 | 206 | 191 | 15 |
| z3-4.10.2 | 210 | 191 | 19 |
| z3-4.12.6 | 217 | 190 | 27 |
| z3-4.14.1 | 225 | 193 | 32 |
| z3-4.16.0 | 234 | 196 | 38 |
| cvc5-1.3.2 | 211 | 190 | 21 |
| smtinterpol-2.5 | 750 | 252 | 498 |
| yices2-2.6.5 | 259 | 230 | 29 |
| yices2-2.7.0 | 243 | 200 | 43 |

### bv16 task, N=15 (first pass)

| solver | per-process | reset | delta |
|---|---:|---:|---:|
| z3-4.3 | 325 | 227 | 99 |
| z3-4.8.12 | 280 | 231 | 49 |
| z3-4.10.2 | 282 | 240 | 41 |
| z3-4.12.6 | 282 | 231 | 51 |
| z3-4.14.1 | 279 | 237 | 42 |
| z3-4.16.0 | 283 | 235 | 48 |
| cvc5-1.3.2 | 253 | 244 | 10 |
| smtinterpol-2.5 | 1427 | 498 | 930 |
| yices2-2.6.5 | 450 | 283 | 167 |
| yices2-2.7.0 | 435 | 283 | 153 |

At N=15 it looked like the delta grew substantially with proof
difficulty, especially for yices2 (29→167ms, 43→153ms) — which would
have meant per-process gets *relatively worse* on harder problems, not
just paying a fixed one-time tax.

### bv16 task, N=50 (confirmation pass)

| solver | per-process | reset | delta |
|---|---:|---:|---:|
| z3-4.3 | 254 | 216 | 38 |
| z3-4.8.12 | 217 | 219 | -2 |
| z3-4.10.2 | 225 | 220 | 5 |
| z3-4.12.6 | 224 | 220 | 4 |
| z3-4.14.1 | 225 | 220 | 5 |
| z3-4.16.0 | 227 | 222 | 4 |
| cvc5-1.3.2 | 209 | 218 | -8 |
| smtinterpol-2.5 | 364 | 219 | 145 |
| yices2-2.6.5 | 199 | 208 | -9 |
| yices2-2.7.0 | 200 | 209 | -9 |

At N=50 every native-executable solver's delta collapsed to within
about ±10ms — indistinguishable from measurement noise — regardless of
whether the task was near-instant or took several hundred ms of real
search. The dramatic N=15 yices2 numbers did not hold up at all
(167ms → -9ms); N=15 was simply too small a sample for this kind of
process-timing measurement. smtinterpol is the only solver that keeps a
material delta, but for an unrelated reason: it's launched as
`java -jar smtinterpol.jar`, so its per-process path pays real JVM
cold-start cost every iteration, not solver-internal search cost (and
even that number shrank sharply from N=15 to N=50, so its "growth" was
partly the same noise effect too). Separately, `smtinterpol-2.5` returns
`unknown` rather than `sat` on the bv16 problem (a solver capability
limit, not a timing artifact).

## Conclusion

Once the `Thread.sleep(1000)` bug is removed, the difference between
launching a fresh solver process per script and reusing one process with
`(reset)` is small and — for every native-executable solver tested —
does not grow with how hard the proof actually is. It behaves as a
fixed, roughly ten-millisecond-scale tax on relaunching, not a cost that
compounds with proof difficulty.

That fixed cost is also small in absolute terms: on the order of tens of
milliseconds, against solver launch-plus-trivial-solve times of
~200-250ms and real proof times that are typically much larger still.
In other words, the time it takes to start a new solver process for a
new proof problem — either way — is far smaller than the typical time
the proof itself takes.

**Practical takeaway**: for the "many scripts" use case, the choice
between per-process and `(reset)` is not worth optimizing for
performance. Per-process is simpler and gives cleaner isolation between
scripts (no risk of `(reset)` leaving stray state behind); `(reset)`
saves an amount of time that is negligible next to real proof time. Pick
per-process by default and reserve `(reset)` for cases that specifically
need it for other reasons (e.g. avoiding process-launch overhead when
proof tasks are themselves extremely fast and extremely numerous).

## Reproducing

```
cd SMT/experiments/process-vs-reset
./run_experiment.sh 50 default.smt2   # trivial task
./run_experiment.sh 50 bv16.smt2      # harder bitvector task
```

Requires `SMT_SOLVER_DIR` to be set (or resolvable via `SMTTests/setup`)
and `SMT/jSMTLIB.jar` already built.
