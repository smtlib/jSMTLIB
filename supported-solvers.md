# Supported SMT solvers

There are a variety of SMT solvers. In fact there is an annual competition
([SMT-COMP](https://smt-comp.github.io)) to evaluate the capabilities and
performance of publicly available solvers. The jSMTLIB tool works with the
solvers contained in the [SMTLIB/Solvers](https://github.com/SMTLIB/Solvers)
GitHub repository. The supported solvers are listed here by platform (as of
this writing). There are more solvers than listed here or supported by this
tool. Note that solvers have varying capabilities, from specific to certain
logics to very general.

`smtinterpol` is a Java archive and so runs on every platform. The Windows
builds are supplied as `.exe` files.

| Solver | Linux x86-64 | Linux arm64 | macOS x86-64 | macOS arm64 | Windows |
|:---|:---:|:---:|:---:|:---:|:---:|
| `alt-ergo-2.6.3` | ✓ |  |  | ✓ |  |
| `bitwuzla-0.9.1` | ✓ | ✓ |  | ✓ | ✓ |
| `cvc5-1.3.2` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `Simplify-1.5.4` | ✓ |  |  |  | ✓ |
| `smtinterpol-2.5` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `yices2-2.6.5` | ✓ |  | ✓ | ✓ | ✓ |
| `yices2-2.7.0` | ✓ |  | ✓ | ✓ |  |
| `z3-5.1.0` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `z3-4.16.0` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `z3-4.14.1` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `z3-4.12.6` | ✓ |  | ✓ | ✓ | ✓ |
| `z3-4.10.2` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `z3-4.8.12` | ✓ | ✓ | ✓ | ✓ | ✓ |
| `z3-4.7.1` | ✓ |  | ✓ |  | ✓ |
| `z3-4.6.0` | ✓ |  | ✓ |  |  |
| `z3-4.5.0` | ✓ |  | ✓ |  |  |
| `z3-4.3.2` |  | ✓ |  |  | ✓ |
| `z3-4.3.1` | ✓ | ✓ | ✓ | ✓ |  |
| `z3-4.3.0` | ✓ |  |  |  |  |

*This table is generated from the contents of the Solvers repository;
see `gen-supported-solvers` in the gh-pages branch.*
