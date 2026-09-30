# SMT solver logic-name support, all platforms

Combined from `logics-report.py --json` runs on: `linux-arm64`, `linux-x86_64`, `macos-arm64`, `macos-x86_64`, `windows`.

Each platform only ships some of the solver binaries, so `-` (no such binary here) is a different answer from `n` (the solver rejected the logic).

| | meaning |
|:---:|:---|
| `Y` | accepted -- the solver answered `success` |
| `A` | accepted, but this solver accepts any string, valid logic or not |
| `n` | rejected -- `unsupported`, an error, or no response |
| `?` | ambiguous response, or the probe timed out |
| `-` | this platform ships no such solver binary |
| `!` | platforms disagree; see the consistency section |
| `x` | binary present but unusable on every platform that has it |

## Cross-platform consistency

**7 disagreement(s)** -- the same solver version reached different verdicts on different platforms. Each is either a genuinely platform-specific build difference or a flaky probe (most often a timeout, which grades as ambiguous).

| Solver | Logic | Verdicts by platform |
|:---|:---|:---|
| `yices2 2.6.5` | `QF_NIA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |
| `yices2 2.6.5` | `QF_NRA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |
| `yices2 2.6.5` | `QF_UFNRA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |
| `yices2 2.6.5` | `QF_ANIA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |
| `yices2 2.6.5` | `QF_AUFNIA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |
| `yices2 2.6.5` | `QF_NIRA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |
| `yices2 2.6.5` | `QF_UFNIA` | n rejected: windows; Y accepted: linux-x86_64, macos-arm64, macos-x86_64 |

## Unusable binaries

These binaries are present but produced no usable verdict on any row: every probe timed out. That is one fact about the binary on that platform, not a per-logic result, so these are excluded from the consistency check above and shown as `x` below.

| Solver | Platform |
|:---|:---|
| `z3 4.3.1` | linux-arm64 |
| `z3 4.3.2` | linux-arm64 |

## Solver availability

| Solver | linux-arm64 | linux-x86_64 | macos-arm64 | macos-x86_64 | windows |
|:---|:---:|:---:|:---:|:---:|:---:|
| `alt-ergo 2.6.3` | - | Y | Y | - | - |
| `bitwuzla 0.9.1` | Y | Y | Y | - | Y |
| `cvc5 1.3.2` | Y | Y | Y | Y | Y |
| `smtinterpol 2.5` | Y | Y | Y | Y | Y |
| `yices2 2.6.5` | - | Y | Y | Y | Y |
| `yices2 2.7.0` | - | Y | Y | Y | - |
| `z3 4.3.0` | - | Y | - | - | - |
| `z3 4.3.1` | Y | Y | Y | Y | - |
| `z3 4.3.2` | Y | - | - | - | Y |
| `z3 4.5.0` | - | Y | - | Y | - |
| `z3 4.6.0` | - | Y | - | Y | - |
| `z3 4.7.1` | - | Y | - | Y | Y |
| `z3 4.8.12` | Y | Y | Y | Y | Y |
| `z3 4.10.2` | Y | Y | Y | Y | Y |
| `z3 4.12.6` | - | Y | Y | Y | Y |
| `z3 4.14.1` | Y | Y | Y | Y | Y |
| `z3 4.16.0` | Y | Y | Y | Y | Y |
| `z3 5.1.0` | Y | Y | Y | Y | Y |

## Logic acceptance

Where a solver version exists on several platforms and they agree, the shared verdict is shown. A disagreement is shown as `!` and listed above.

`A` marks `bitwuzla 0.9.1`, `z3 4.3.0`, `z3 4.3.1`, `z3 4.3.2`: these accept the invalid control logic too, so they do not validate the `set-logic` argument at all, and an acceptance says nothing about the specific logic named.

| Group | Logic | `alt-ergo 2.6.3` | `bitwuzla 0.9.1` | `cvc5 1.3.2` | `smtinterpol 2.5` | `yices2 2.6.5` | `yices2 2.7.0` | `z3 4.3.0` | `z3 4.3.1` | `z3 4.3.2` | `z3 4.5.0` | `z3 4.6.0` | `z3 4.7.1` | `z3 4.8.12` | `z3 4.10.2` | `z3 4.12.6` | `z3 4.14.1` | `z3 4.16.0` | `z3 5.1.0` |
|:---|:---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| Baseline | `(default)` | n | A | Y | n | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `ALL` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
| Official | `AUFLIA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `AUFLIRA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `AUFNIRA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `LIA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `LRA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_ABV` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_AUFBV` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_AUFLIA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_AX` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_BV` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_EIA` | n | A | n | n | n | n | A | A | A | n | n | n | n | n | n | n | n | n |
|  | `QF_FP` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_IDL` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_LIA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_LRA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_NIA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_NRA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_RDL` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UF` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UFBV` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UFIDL` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UFLIA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UFLRA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UFNRA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UFLRA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UFNIA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
| Unofficial | `ALIA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `BV` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `NIA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `NRA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_ALIA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_ANIA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_AUFNIA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_BVFP` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_LIRA` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_NIRA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `QF_UFNIA` | n | A | Y | Y | ! | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UF` | n | A | Y | Y | Y | Y | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UFBV` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UFIDL` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UFLIA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
|  | `UFNRA` | n | A | Y | Y | n | n | A | A | A | Y | Y | Y | Y | Y | Y | Y | Y | Y |
| Control | `ZZZ` | n | A | n | n | n | n | A | A | A | n | n | n | n | n | n | n | n | n |

*Generated by `SMTTests/reports/combine-logics-reports.py`.*
