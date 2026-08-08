# SMTTests

Test suite for jSMTLIB.  Tests are driven either by JUnit (preferred) or by
the legacy bash scripts described below.

---

## Running tests

### Primary entry point

```
make test
```

Runs the full JUnit suite via `./runjunits`.  This is the normal way to run all tests.

### Individual Makefile targets

| Target | What it does |
|--------|-------------|
| `make test` / `make tests` | Run the full JUnit suite (`junit-tests`) |
| `make junit-tests` | Compile and run all JUnit test classes via `./runjunits` |
| `make smt-tests` | Run `.tst` file tests using the legacy bash `./runtests` script (useful for diagnosing a specific failure — bash diffs are easier to read than JUnit comparison output) |
| `make script-tests` | Run `.scr` script tests using the legacy bash `./runscripts` script (same rationale) |
| `make build` | Build `../SMT/jSMTLIB.jar` |
| `make clean` | Remove `*.actual` output files and compiled test classes |
| `make cov-test` | Run all tests under JaCoCo coverage instrumentation |
| `make cov-report` | Merge `.exec` files and generate HTML + XML coverage report |
| `make cov-show` | Open the HTML coverage report in the default browser |
| `make cov-all` | `cov-clean` + `cov-test` + `cov-report` + `cov-show` in one step |

---

## JUnit test classes

All classes are under `src/org/smtlib/test/`.

### `UnitTests`
Plain JUnit, no parameterization, no solver.  Tests `Log` listener lifecycle and
`Utils.quote` / `Utils.unescape`.

### `RoundTripTest`
Plain JUnit, no parameterization, no solver.  Parses every command in
`roundtrip.smt2`, reprints each via `org.smtlib.sexpr.Printer`, and asserts
the output exactly reproduces the input.  Exercises all `write()` implementations
without starting any solver process.

### `ParseCommand`
Plain JUnit, no parameterization, no solver.  Tests command parsing in isolation
via the type-checker.

### `FileTests`
Parameterized by `(solver, tst-file)`.  Discovers every `.tst` file under
`tests/` recursively, and runs each one against each solver in `SOLVERS`
(`test` and `z3_4_3` currently).  Runs the SMT engine in-process (no JVM
fork per test), which is why the full suite finishes in ~4 minutes instead
of the ~10 minutes that `make smt-tests` takes.

Golden file priority matches `runtest` exactly (see comment in `findGoldenFile`
and in `runtest`).  Skip files (`.skip`, `.skip.<platform>`, etc.) are honoured.

### `ScriptTests`
Parameterized by script file.  Discovers every `.scr` file under `scripts/`
and runs each one by invoking `bash runscript <path>`.  No solver
parameterization — each script hardcodes its own solver invocation.  Exit code
77 from `runscript` maps to a JUnit skip; any other non-zero exit is a failure.

---

## Legacy bash scripts

These remain useful for examining the diff output when a test fails, since JUnit
only shows the comparison mismatch at the end of the run.

| Script | Purpose |
|--------|---------|
| `./runtests [--solvers "s1 s2"]` | Run `.tst` tests via one JVM process per test |
| `./runtest <solver> <file.tst>` | Run a single `.tst` test |
| `./runscripts [file.scr ...]` | Run all (or named) `.scr` script tests |
| `./runscript <file.scr>` | Run a single `.scr` script test (exits 0/77/1) |
| `./runjunits` | Compile and run the JUnit suite directly |
