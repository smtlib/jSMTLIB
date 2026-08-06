# V2.0 Logic Archive

This directory contains SMT-LIB logic definition files that are not part of the
current SMT-LIB standard but are recognized by major SMT solvers.

## Origin

These 18 files were added to jSMTLIB in June 2015 (commit c7837e8, "Adding
support for yices2 and z3-4.4") to allow jSMTLIB to accept `set-logic` commands
using logic names that those solvers recognize but that are not defined on
smt-lib.org.

They are labeled V2.0 because the version strings inside them carry
`:smt-lib-version 2.0`, but most were not part of the jSMTLIB distribution
before 2015 — they were added specifically for solver compatibility.

## Status in the SMT-LIB Standard

None of these logic names appear on smt-lib.org/logics.shtml (checked August
2026) or in the GitHub repository SMT-LIB/SMT-LIB-2, which dates back to 2015
and has never contained them. They are absent from the standard at least since
SMT-LIB 2.5 (April 2015).

Note: Several of these names (QF_UFNIA, NRA, ALIA, QF_ALIA and possibly others)
do appear in the logic inclusion diagram on smt-lib.org even though they have no
downloadable `.smt2` file there.

Sources:
- https://smt-lib.org/logics.shtml
- https://github.com/SMT-LIB/SMT-LIB-2

## Solver Support

### Yices2

14 of the 18 logic names are explicitly listed in Yices2's internal logic code
table (`src/api/smt_logic_codes.h`) and documentation. The exceptions are
`QF_BVFP`, `QF_FP` (Yices2 has no floating-point support), and
`Fixed_Size_BitVectors` (not a recognized name).

Sources:
- https://yices.csl.sri.com/doc/smt-logics.html
- https://github.com/SRI-CSL/yices2/blob/master/src/api/smt_logic_codes.h

### Z3

16 of the 18 logic names appear in Z3 source or release notes. `QF_FP` and
`QF_BVFP` are explicitly supported in `smt_setup.cpp`. Z3 also uses substring
matching on logic names, so it will functionally accept most combinations.
`Fixed_Size_BitVectors` does not appear in Z3 source or documentation.

Sources:
- https://github.com/Z3Prover/z3/blob/master/src/solver/smt_logics.cpp
- https://github.com/Z3Prover/z3/blob/master/src/smt/smt_setup.cpp
- https://github.com/Z3Prover/z3/blob/master/RELEASE_NOTES.md

## File Notes

| File | Yices2 | Z3 | Notes |
|------|--------|----|-------|
| ALIA.smt2 | yes | yes | |
| BV.smt2 | yes | yes | |
| Fixed_Size_BitVectors.smt2 | no | no | Old underscore form of FixedSizeBitVectors; predates 2015 in jSMTLIB |
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
