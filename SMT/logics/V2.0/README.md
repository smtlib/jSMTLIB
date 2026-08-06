# V2.0 Logic Archive

This directory is an archive of the jSMTLIB logic and theory definition files as
they existed just before SMT-LIB 2.5 support was added. The content matches
commit `efd0b16` ("CLeaning up tests and responses to tests", 2015-06-27), which
is the last commit before V2.5 work began.

All files carry `:smt-lib-version 2.0` and are used by jSMTLIB when the
configured SMT-LIB version is set to V2.0 (e.g. via `set-info :smt-lib-version
"V2.0"`), so that logic and theory version checks pass correctly.

## File Contents

The directory contains 49 files in two groups:

### Standard SMT-LIB 2.0 logic and theory files (30 files)

These were present in jSMTLIB from the initial commit (`5a05f55`, 2015-06-24)
and are unchanged through `efd0b16`:

`AUFLIA`, `AUFLIRA`, `AUFNIRA`, `ArraysEx`, `Core`, `Fixed_Size_BitVectors`,
`FloatingPoint`, `Ints`, `LIA`, `LRA`, `QF_ABV`, `QF_AUFBV`, `QF_AUFLIA`,
`QF_AX`, `QF_BV`, `QF_IDL`, `QF_LIA`, `QF_LRA`, `QF_NIA`, `QF_NRA`,
`QF_RDL`, `QF_UF`, `QF_UFBV`, `QF_UFIDL`, `QF_UFLIA`, `QF_UFLRA`,
`QF_UFNRA`, `Reals`, `Reals_Ints`, `UFLRA`, `UFNIA`

### Non-standard solver-compatibility logic files (19 files)

These were added in commit `c7837e8` ("Adding support for yices2 and z3-4.4",
2015-06-26) to allow jSMTLIB to accept `set-logic` commands using logic names
recognized by Yices2 and Z3 but not defined on smt-lib.org:

`ALIA`, `BV`, `NIA`, `NRA`, `QF_ALIA`, `QF_ANIA`, `QF_AUFNIA`, `QF_BVFP`,
`QF_FP`, `QF_LIRA`, `QF_NIRA`, `QF_UFNIA`, `UF`, `UFBV`, `UFIDL`, `UFLIA`,
`UFNRA`, `FloatingPoint`, `LIA`

None of these logic names appear on smt-lib.org/logics.shtml or in the GitHub
repository SMT-LIB/SMT-LIB-2 (absent from the standard since at least SMT-LIB
2.5, April 2015). Several names (QF_UFNIA, NRA, ALIA, QF_ALIA and possibly
others) appear in the smt-lib.org logic inclusion diagram but have no
downloadable `.smt2` file there.

#### Solver support for non-standard logics

| File | Yices2 | Z3 | Notes |
|------|--------|----|-------|
| ALIA.smt2 | yes | yes | |
| BV.smt2 | yes | yes | |
| Fixed_Size_BitVectors.smt2 | no | no | Old underscore form of FixedSizeBitVectors |
| NIA.smt2 | yes | yes | |
| NRA.smt2 | yes | yes | |
| QF_ALIA.smt2 | yes | yes | |
| QF_ANIA.smt2 | yes | yes | |
| QF_AUFNIA.smt2 | yes | yes | |
| QF_BVFP.smt2 | no | yes | Floating-point; Yices2 has no FP support |
| QF_FP.smt2 | no | yes | Floating-point; Yices2 has no FP support |
| QF_LIRA.smt2 | yes | yes | |
| QF_NIRA.smt2 | yes | yes | |
| QF_UFNIA.smt2 | yes | yes | |
| UF.smt2 | yes | yes | |
| UFBV.smt2 | yes | yes | Also known as QBVF in some Z3 contexts |
| UFIDL.smt2 | yes | yes | |
| UFLIA.smt2 | yes | yes | |
| UFNRA.smt2 | yes | yes | |

Sources:
- https://smt-lib.org/logics.shtml
- https://github.com/SMT-LIB/SMT-LIB-2
- https://yices.csl.sri.com/doc/smt-logics.html
- https://github.com/SRI-CSL/yices2/blob/master/src/api/smt_logic_codes.h
- https://github.com/Z3Prover/z3/blob/master/src/solver/smt_logics.cpp
- https://github.com/Z3Prover/z3/blob/master/src/smt/smt_setup.cpp
