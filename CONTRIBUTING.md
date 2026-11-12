# Contributing to jSMTLIB

## Questions, bugs and feature requests

- Bugs, feature requests and questions: [GitHub Issues](https://github.com/smtlib/jSMTLIB/issues). For a bug,
  include the jSMTLIB version (`java -jar jSMTLIB.jar --version`), the solver and its version, the command
  line, and the smallest SMT-LIB input that shows the problem.
- Security vulnerabilities: see [SECURITY.md](SECURITY.md); do not open a public issue.

## Code changes

Changes are made by pull request against the `dev` branch. `master` holds releases.

- The build needs a JDK and `make`. In `SMT/`, `make build` builds `jSMTLIB.jar`.
- `make test` (in `SMT/` or `SMTTests/`) runs the JUnit suite against the built jar. By default it uses only
  jSMTLIB's built-in test solver; `SMT_TEST_SOLVERS` adds real solvers, whose binaries come from the
  [Solvers](https://github.com/smtlib/Solvers) repository, located by `SMT_SOLVER_DIR`
  (see [SMTTests/README.md](SMTTests/README.md)).
- CI builds and tests each push to `dev` and `master` on Linux, macOS and Windows.

## Requirements for a pull request

- **Tests.** Every bug fix comes with a regression test that fails without the fix; every new feature comes
  with tests of it. The full suite passes. Prefer a `.tst` file (an SMT-LIB script with golden output) over a
  `.scr` script, and either over a JUnit test; [SMTTests/README.md](SMTTests/README.md) describes each kind.
- **Conformance.** jSMTLIB follows the [SMT-LIB standard](https://smt-lib.org). A solver adapter makes its
  solver behave as close to the standard as it can, and reports what the solver does not support.
- **An issue.** Reference the issue the change addresses in the commit message or pull request.
- **Style.** Follow the surrounding code: 4-space indentation, no tabs.
- **Licensing.** Contributions are accepted under the project's license (see [LICENSE](LICENSE)).
