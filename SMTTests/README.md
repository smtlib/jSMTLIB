# SMTTests

Test suite for jSMTLIB. All tests run as JUnit (`make test`); a couple of legacy
bash-driven paths remain for interactive debugging (see below).

CAUTION: The test infrastructure is not yet thread-safe.  Tests can be run sequentially,
or concurrently in separate JVMs, but the JUnit tests may not be run reliably in parallel.

---

## Running tests

### Primary entry point

```
make test
```

Compiles and runs the full JUnit suite via `./runjunits`. `runjunits` discovers
test sources **dynamically**: every `.java` file under `src/org/smtlib/test/`
is compiled, and any file containing at least one `@Test` annotation is added
to the run list automatically. Adding a new test class needs no script edit —
just put the test .java file in `src/org/smtlib/test` and 
give it at least one `@Test` method and it's picked up on the next run.

### Which solvers get exercised

One environment variable, `SMT_TEST_SOLVERS`, is the single controlling place
for which solvers the parameterized test classes (`FileTests`,
`LogicsBadPath`, and any future class that extends `LogicTests`) run
against. (`LogicsWithPath`, which extends the separate, unparameterized
`LogicsBase` instead, always runs against the built-in `test` solver only —
see its own entry below. `TypeCheckTests`, which extends `FileTests` but
overrides `datax()` entirely, likewise always runs against `test` only,
deliberately — see the `typechecks/` section above.) It's a space-separated list of solver
names (as configured in `jsmtlib.properties`); default is just `test`
(the built-in pure-Java solver that needs no external binary),
if not set to another default in the Makefile:

```
make test                                          # SMT_TEST_SOLVERS=test (default)
make test SMT_TEST_SOLVERS="test z3-4.3"           # add a real solver
SMT_TEST_SOLVERS="test z3-4.3" bash ./runjunits     # same, without make
```

`runjunits` prints `Solvers: ...` at the start of every run so it's always
visible which solvers a given run actually covers. `./runtests` (the legacy
`.tst` runner, see below) honors the same variable, so `make smt-tests` and
`make test` stay in sync without needing separate configuration.

### Individual Makefile targets

| Target | What it does |
|--------|-------------|
| `make test` / `make tests` | Run the full JUnit suite (`junit-tests`) |
| `make junit-tests` | Compile and run all JUnit test classes via `./runjunits` |
| `make smt-tests` | Run `.tst` file tests using the legacy bash `./runtests` script (useful for diagnosing a specific failure — bash diffs are easier to read than JUnit comparison output) |
| `make script-tests` | Run `.scr` script tests using the legacy bash `./runscripts` script (same rationale) |
| `make build` | Build `../SMT/jSMTLIB.jar` |
| `make clean` | Remove all generated compilation, coverage and test artifacts |
| `make cov-test` | Run all tests under JaCoCo coverage instrumentation |
| `make cov-report` | Merge `.exec` files and generate HTML + XML coverage report |
| `make cov-show` | Open the HTML coverage report in the default browser |
| `make cov-all` | `cov-clean` + `cov-test` + `cov-report` + `cov-show` in one step |

`SMT_SOLVER_DIR` (also exported by the Makefile) is a separate variable: it
points at the directory holding the actual solver binaries/executables for
this platform, resolved from `../../OpenJML21/Solvers/<platform>` by default
unless already set in the environment (CI sets it explicitly). `SMT_TEST_SOLVERS`
picks *which* solvers to run; `SMT_SOLVER_DIR` says *where to find* them.

---

## Directory structure

```
SMTTests/
  src/org/smtlib/test/   JUnit test classes (see below)
  tests/                 .tst files: SMT-LIB scripts + golden output, run by FileTests
  typechecks/            .tst files exercising jSMTLIB's own TypeChecker, run by TypeCheckTests
  scripts/               .scr files: shell-driven scenarios, run by ScriptTests
  bin/                   compiled .class output (javac -d target)
  lsp/libs/               junit-4.13.2.jar, hamcrest-core-1.3.jar
```

### `tests/` — `.tst` files, grouped by topic

Each `.tst` file is a literal SMT-LIB command script. `FileTests` runs it via
`smt.exec()` and diffs the captured stdout/stderr against a golden `.out`/`.err`
file. See "Golden file conventions" below for the naming rules.

| Subdirectory | Covers |
|---|---|
| `tests/` (top level, ~34 files) | Miscellaneous: echo, ite, quantifier/pattern parsing, misc error cases |
| `array/` | Array theory (`select`/`store` axioms) |
| `bv/` | Bit-vector literals and operations |
| `datatype/` | `declare-datatype(s)`, constructors/selectors, well-foundedness |
| `declare/` | `declare-fun`/`declare-sort`/`declare-const` syntax and errors |
| `define/` | `define-fun`/`define-sort`/`define-fun-rec`/`define-funs-rec` |
| `getAssertions/` | `get-assertions` |
| `getAssignment/` | `get-assignment` |
| `getInfo/` | `get-info` (`:authors`, `:name`, `:version`, `:error-behavior`, ...) |
| `getModel/` | `get-model` |
| `getProof/` | `get-proof` |
| `getUnsatCore/` | `get-unsat-core` |
| `getValue/` | `get-value` |
| `getset_option/` | `get-option`/`set-option` for every defined option, including all `:produce-*` options |
| `letTests/` | `let`-bound sat/unsat checks (migrated from `LetTests.java`) |
| `logics/` (largest, ~69 files) | One `ok_<LOGIC>.tst`/`err_<LOGIC>.tst` pair per SMT-LIB logic — `set-logic` acceptance plus per-logic operator/sort legality |
| `match/` | `match` expressions and patterns (including the `_` wildcard) |
| `named/` | `:named` attribute and named-expression scoping |
| `pushpop/` | `push`/`pop` scope handling |
| `quantTests/` | Quantified (`forall`/`exists`) sat/unsat checks (migrated from `QuantTests.java`) — see per-solver golden variants below |
| `satChecks/` | Quantifier-free sat/unsat checks: booleans, LIA, chained comparisons, `ite` (migrated from `SatChecks.java`) |
| `setInfo/` | `set-info`, including pre-defined-keyword rejection |
| `tokens/` | Lexer-level token acceptance/rejection |
| `version/` | SMT-LIB version-specific syntax differences (V2.0 vs V2.5 vs V2.6 vs V2.7) |

`LogicsCoverageTest` (a JUnit test, not a `.tst` file) cross-checks that
`tests/logics/` covers every logic actually shipped under `SMT/logics/` —
run it after adding or renaming a logic file.

### `typechecks/` — `.tst` files exercising jSMTLIB's own `TypeChecker`

A sibling of `tests/`, not a subdirectory of it, and run by a separate class,
`TypeCheckTests` (extends `FileTests`, reusing all its golden/skip/comparison
machinery, overriding only `datax()`: scans `typechecks/` instead of
`tests/`, and pairs every file with the built-in `"test"` solver only — not
parameterized by `SMT_TEST_SOLVERS`, and not cross-producted with real
solvers at all).

That restriction is deliberate, not a placeholder oversight:
`Solver_test.assertExpr()` is the *only* `ISolver` implementation that calls
`TypeChecker.checkAssertion()`. Every real-solver adapter inherits
`AbstractSolver.assertExpr()`, which forwards the asserted text straight to
the solver process and never invokes `TypeChecker` at all — so running these
against a real solver would not exercise the code this directory exists to
check; the solver would just do its own independent native type-checking
(or not) on the same input. That is a real, separate, and interesting
question, deliberately deferred rather than conflated with this one — see
the "Migration" note below.

Ported from the retired `TypeCheck`/`TypeCheckInt`/`TypeCheckBV`/
`TypeCheckRealsInts`/`TypeCheckQuantifiers`/`TypeChecks` JUnit classes (see
the "Parse/typecheck tests" section below for what replaced them and why),
plus a couple of fixes discovered along the way:

- `err_quantExistsMultiError.tst` (ported from `TypeCheckQuantifiers.
  checkBadExists`) documents a real, narrow limitation surfaced by the port:
  the original JUnit test called `TypeChecker.checkAssertion()` directly and
  observed *two* errors from one expression, but `Solver_test.assertExpr()`
  only ever returns `errs.get(0)` — the first — per its own
  `// FIXME - return all errors, not just the first`. A normal `(assert
  ...)` command can never surface more than the first type error for a
  single command, so the ported `.tst` golden reflects only that first
  error; the second is simply not observable this way. Worth a dedicated
  test of that limitation itself in a future pass.
- `err_genericTypeArity_declareFunArg.tst` and
  `err_genericTypeArity_zeroArityUsedWithParam.tst` close a real coverage
  gap found while porting, not just a straight port: a user-declared
  parameterized sort (`(declare-sort X 1)`) referenced later with the wrong
  number of type arguments was untested anywhere — `tests/declare/
  err_declareSort*.tst` only covers malformed `declare-sort` syntax and
  re-declaration, and `tests/array/array2/err_array2_arity*.tst` only
  covers the arity of the built-in `Array` sort.

**Migration status**: this is step (a) of a three-step plan. (a) — port the
existing `TypeCheck*` JUnit tests faithfully, done. (b) — expand coverage to
the rest of `TypeChecker`'s ~55 error-producing call sites (match
expressions, datatypes, sort-abbreviation and numeral/literal-format errors
are all currently under-tested or untested), and cross-check against what
the SMT-LIB standard itself actually requires be rejected, not just what
`TypeChecker.java` happens to implement — not yet started. (c) — eventually,
run this same `.tst` corpus against real solvers too, to see how completely
each one's own native type-checking compares (a genuinely different
question from this directory's, per the mechanism explanation above,
capturing its own real per-solver goldens) — not yet started, blocked on
(b).

### `scripts/` — `.scr` files

Shell-driven scenarios that need more than one `$SMT_CMD` invocation, or
specific command-line flags, in a single test — things `.tst`'s single-process
model can't express. `ScriptTests` discovers and runs every `.scr` file.
Examples: `logic-validation.scr` (4-part `-L` path scenario), `driver-*.scr`,
`interactive-*.scr`, `port-*.scr`, `props*.scr` (properties-file resolution).

---

## JUnit test classes (`src/org/smtlib/test/`)

### Script/file execution engines

| Class | What it runs |
|---|---|
| **FileTests** | Every `.tst` file under `tests/`, parameterized by `(solver, file)` from `LogicTests.solvers` (i.e. `SMT_TEST_SOLVERS`). Runs in-process (no JVM fork per test). |
| **ScriptTests** | Every `.scr` file under `scripts/`, via `bash runscript <path>`. No solver parameterization — each script hardcodes its own. Exit 77 → JUnit skip. |
| **SMTCommandLineTests** | Spawns real `SMT_CMD` subprocesses with specific CLI flags (`-L`, `--logics`, malformed custom logic/theory files in a temp dir, etc.) — tests command-line argument handling and logic/theory file validation directly, which `.tst` has no mechanism to vary per-file. |

### Solver-response tests (parameterized over solver × SMT-LIB version)

All extend `LogicTests` (or `LogicsBase`) and drive the solver command-by-command
via `doCommand(input, expectedResult)`, asserting each response directly rather
than diffing a whole script's output.

| Class | Covers |
|---|---|
| **LogicsWithPath** | `set-logic` acceptance for every logic name, plus the deliberately-bogus `ZZZ` not-found case, with an explicit `logicPath` set to a real directory (`../SMT/logics`) — exercises the explicit-path branch of `Utils.openLogicStream`, and is the only place that confirms the full logic-name set actually resolves end-to-end through that branch against the real production logic files (not just synthetic temp-dir content, see `SMTCommandLineTests` below). |
| **LogicsBadPath** | Same, but with a deliberately-invalid `logicPath` (`"xxx"`) — exercises the upfront path-component validation in `Utils.openLogicStream` (`"Invalid logic path: ... is not a directory"`). |

`SatChecks`, `LetTests`, and `QuantTests` used to be part of this family;
they've been migrated to `tests/satChecks/`, `tests/letTests/`, and
`tests/quantTests/` respectively and no longer exist as Java classes.
`InfoOptions` (`get-info`/`get-option`/`set-option` round trips and
per-solver reported values) has likewise been retired: every check it made
was already duplicated, and generally more precisely, by `tests/getInfo/`
and `tests/getset_option/` `.tst` files (`ok_getInfo.tst`, `err_setInfo.tst`,
`ok_printSuccess.tst`, `ok_allDefinedOptions.tst`, `ok_setOptionalOptions.tst`,
`ok_setRequiredOptions.tst`, `ok_getRequiredOptions.tst`,
`ok_set_produceOptions.tst`, `ok_getOption.tst`), which also cover
`:global-declarations`, `:produce-unsat-assumptions`, and
`:reproducible-resource-limit` that `InfoOptions` never tested at all. Two
caveats worth knowing: (1) `:print-success` and `:regular`/`:diagnostic-
output-channel` are coopted entirely client-side by jSMTLIB (see
`AbstractSolver.checkPrintSuccess`/`set_option`), so neither `InfoOptions`
nor these `.tst` files ever observed a real solver's native behavior for
those three options — that's covered separately, by bypassing jSMTLIB
entirely, in `scripts/solverBehavior/print-success.scr` and
`solver-output-channel.scr`; the `.tst` versions are still worth keeping as
regression tests of jSMTLIB's own client-side option-handling code. (2)
`InfoOptions` parameterized over `SMTLIB` version as well as solver, but
only `:interactive-mode`/`:produce-assertions` actually branched on it, and
empirically neither option's availability turned out to depend on the
declared version in practice — so nothing meaningful was lost by not
replicating that dimension in the `.tst` files, which run under whichever
SMT-LIB version is ambient by default.

`Logics` (the no-explicit-`logicPath` sibling of `LogicsWithPath`, both
extending `LogicsBase`) has also been retired: it hardcoded
`solvername = "test"` (never exercised a real solver), and its own
`checkResponse` helper doesn't actually assert anything for a successful
`set-logic` — only the error path does a real string comparison — so in
practice it only ever verified "no error" for the success cases. All 24
real logic names it covered have an exact `tests/logics/ok_<NAME>.tst`
counterpart; `ALL` is covered by `ok_setLogic_ALL.tst` and is also the
working logic in dozens of other `.tst` files across the suite; the
deliberately-bogus `ZZZ` case is covered by `err_setLogic.tst`'s
`(set-logic Q)` line, same error-message format with a different
placeholder name. The `.tst` versions are strictly stronger: they diff the
full response text (not just "didn't error"), and run through `FileTests`'
`SMT_TEST_SOLVERS` parameterization and jSMTLIB's normal `smt.exec()`
script pipeline, rather than `Logics`' single bare
`command.execute(solver)` call against the fixed `test` solver.
(`LogicsBase.data()` also carries a separate, still-open question,
predating and independent of this retirement: several once-valid logic
names — `ALIA`, `BV`, `NIA`, `NRA`, `QF_ALIA`, `QF_ANIA`, `QF_AUFNIA`,
`QF_LIRA`, `QF_NIRA`, `UF`, `UFBV`, `UFIDL`, `UFLIA`, `UFNRA`, `QF_UFNIA`
— are commented out there because they have no `.smt2` file under the
current `SMT/logics`; whether any should be restored, e.g. as
older/non-standard logic names, hasn't been investigated. `LogicsBase.java`
itself is kept, since `LogicsWithPath` still extends it.)

### Parse/typecheck tests (no solver semantics)

These test a layer `.tst`'s response-diffing can't reach: exact print-round-trip
fidelity, or bare-expression parsing outside any command context.

| Class | Covers |
|---|---|
| **RoundTripTest** | Parses every command in `roundtrip.smt2`, reprints via `Printer`, asserts byte-identical output — exercises every command `write()` branch. |
| **ParseCommand** | Parses + typechecks + reprints full commands in isolation (no solver); covers both successful round-trips and `TypeChecker.validate()` error messages. |
| **ParseExpressions** | Parses bare expression/attribute-value fragments directly (`p.parseExpr()`), not wrapped in a command; asserts print-round-trip. |
| **ParseExpressionErrors** | Same, for malformed input — asserts the resulting `(error "...")` response and position. Catches `ParserException` at its own top level (mirroring what `parseCommand()` does internally), since `parseExpr()`/`parseAttributeValue()` throw rather than log-and-return-null. |

`TypeCheck`, `TypeCheckBV`, `TypeCheckInt`, `TypeCheckQuantifiers`,
`TypeCheckRealsInts`, and `TypeChecks` (which called `TypeChecker.
checkAssertion()` directly against a symbol table, bypassing the normal
`ICommand.execute()` pipeline, to check type-checking of asserted
expressions per sort/theory — `TypeChecks` specifically covered
duplicate-name scope-tracking errors that the parser alone can't produce)
have been retired in favor of `typechecks/*.tst`, run by the new
`TypeCheckTests` class — see the `typechecks/` section above for the full
migration rationale and status.

### Pure Java-API unit tests (no SMT-LIB syntax involved)

| Class | Covers |
|---|---|
| **UnitTests** | `Log` listener add/remove/clear lifecycle; `Utils.quote`/`Utils.unescape` string-escaping rules (V2.0 vs V2.5), called directly as Java methods. |
| **PrinterCoverageTest** | Directly constructs internal objects that can never arise from parsing SMT-LIB text (`ISort.IFamily`/`IAbbreviation`/`IFcnSort`, structured `IResponse` subtypes built via factory calls, `Sexpr.Token`/`Expr`) and checks their `toString()`. |
| **RunTests** | Spawns `bash api.sh` (the standalone Java API usage example) via `ProcessBuilder`, checking it runs without throwing. |
| **LogicsCoverageTest** | Infrastructure self-check: every logic `SMT/logics/*.smt2` ships (searched recursively, but deliberately excluding the `V2.0/` subfolder — those logics have no `tests/logics/` coverage yet, a known, self-acknowledged gap) must have matching `(set-logic ...)` coverage somewhere under `tests/logics/`. |

### Infrastructure / base classes (no `@Test` methods, not run directly)

| Class | Purpose |
|---|---|
| **JUnitListener** | `Log.IListener` implementation shared by many test classes to capture logged error responses for assertions. |
| **LogicTests** | Base class for the solver-response family: owns `solvers` (from `SMT_TEST_SOLVERS`), the solver × `SMTLIB.values()` parameterization matrix, `doCommand()`, and `checkResponse()`. |
| **LogicsBase** | Parallel base class (predates/duplicates some of `LogicTests`), used only by `LogicsWithPath` now that `Logics` has been retired (`LogicsBadPath` extends `LogicTests`, not this); hardcodes `solvername = "test"` and owns the logic-name list. |

---

## Golden file conventions (for `.tst` files under `tests/`)

For a test file `foo.tst`, `FileTests`/`runtest` look for output goldens in
this priority order (most-specific first), falling back to the bare file:

```
foo.tst.out.<solver>.<platform-arch>
foo.tst.out.<solver>.<platform>
foo.tst.out.<solver>
foo.tst.out.<platform-arch>
foo.tst.out.<platform>
foo.tst.out                      <- bare default, used by any solver without its own override
```

(same pattern for `.err`). Rules of thumb:
- The **bare** `.out` should hold the mathematically accurate answer (e.g. the
  real `sat`/`unsat`), not a weaker solver's `unknown` — add a solver-specific
  override for any solver that can't determine it, rather than degrading the
  default.
- Don't add a solver-specific override that's identical to the bare default —
  `FileTests` already falls back to bare for any solver without its own file.
- `foo.tst.skip`, `foo.tst.skip.<solver>`, `foo.tst.skip.<platform>`, etc. skip
  the test entirely (as a JUnit `Assume` failure) for that scope; file content
  is the skip reason, shown in the JUnit output.
- A trailing `.bad` variant (e.g. `foo.tst.out.z3-4.3.bad`) documents solver
  output that is genuinely non-conforming (not just differently-worded) --
  e.g. a claimed success that silently didn't take effect. `findGoldenFile`
  consults it as a fallback (after the exact and family goldens, before the
  bare default), so the test still passes deterministically against the
  known-bad output instead of failing every run; promote real conforming
  output to a normal golden instead of `.bad`.

---

## Legacy bash scripts

These remain useful for examining diff output when a test fails, since JUnit
only shows the comparison mismatch at the end of the run.

| Script | Purpose |
|--------|---------|
| `./runtests [--solvers "s1 s2"]` | Run `.tst` tests via one JVM process per test; default solver list comes from `SMT_TEST_SOLVERS` |
| `./runtest <solver> <file.tst>` | Run a single `.tst` test |
| `./runscripts [file.scr ...]` | Run all (or named) `.scr` script tests |
| `./runscript <file.scr>` | Run a single `.scr` script test (exits 0/77/1) |
| `./runjunits` | Compile and run the JUnit suite directly |
| `./setup`, `./setup-coverage` | Sourced by the scripts above; resolve `SMT_DIR`/`SMT_JAR`/`SMT_SOLVER_DIR`/platform, and (for the latter) wire up the JaCoCo coverage agent |
| `version.check` | Sourced by `runtests` and `runscripts`; compares `$SMT_CMD --version` output against `../SMT/version.txt` and feeds an exit code into the overall pass/fail |

`runreport` (LaTeX results-table generator for an old assessment paper) is
kept for historical reference only — not invoked by anything.


