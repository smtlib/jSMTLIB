(logic ALL

 :smt-lib-version 2.5
 :written-by "David Cok"

 :theories (Core ArraysEx Reals_Ints FloatingPoint FixedSizeBitVectors Strings HO-Core)

 ;; This is a special logic that maps to a most general logic supported by the chosen solver.
 ;; ALL itself was introduced in 2.5. Under a configured version it holds that version's copy of
 ;; each listed theory, and omits a theory the version lacks (Strings before 2.6, HO-Core before 2.7).
)


