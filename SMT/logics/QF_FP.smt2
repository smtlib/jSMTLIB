(logic QF_FP

 :smt-lib-version 2.7
 :written-by "jSMTLIB"
 :date "2026-08-16"

 :notes
 "QF_FP is not an official SMT-LIB 2.7 logic -- the SMT-LIB nomenclature lists
  FP (FloatingPoint) as a theory with a logic 'forthcoming', but no QF_FP
  entry exists among the officially published logics (AUFLIA, AUFLIRA,
  AUFNIRA, LIA, LRA, QF_ABV, QF_AUFBV, QF_AUFLIA, QF_AX, QF_BV, QF_EIA,
  QF_IDL, QF_LIA, QF_LRA, QF_NIA, QF_NRA, QF_RDL, QF_UF, QF_UFBV, QF_UFIDL,
  QF_UFLIA, QF_UFLRA, QF_UFNRA, UFLRA, UFNIA). This file was created simply
  to exercise the FloatingPoint theory in jSMTLIB's own test suite, so that
  tests are not forced to use the broad ALL logic.

  It combines FloatingPoint with FixedSizeBitVectors and Reals, rather than
  declaring FloatingPoint alone, because practically every FP operator needs
  one or both: the fp constructor takes three BitVec arguments, several
  to_fp overloads convert from/reinterpret BitVec values, fp.to_ubv/
  fp.to_sbv produce BitVec results, and decimal literals (e.g. 1.0, used to
  build FP values via to_fp) need the DECIMAL sort binding that only Reals/
  Reals_Ints declare -- FloatingPoint.smt2's own :sorts registers the bare
  Real sort but not that literal binding.
 "

:theories (Reals FixedSizeBitVectors FloatingPoint)

:language
 "Closed quantifier-free formulas built over an arbitrary expansion of the
  FloatingPoint, FixedSizeBitVectors, and Reals signatures with free constant
  symbols over the sorts (_ FloatingPoint eb sb) for eb,sb > 1, (_ BitVec m)
  for m > 0, and Real.
 "
)
