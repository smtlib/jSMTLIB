(logic ALL

 :smt-lib-version 2.5
 :written-by "David Cok"

 :theories (Core ArraysEx Reals_Ints FloatingPoint FixedSizeBitVectors Strings HO-Core)

 ;; This is a special logic that maps to a most general logic supported by the chosen solver.
 ;; ALL itself was introduced in 2.5; FloatingPoint FixedSizeBitVectors Strings HO-Core were
 ;; introduced later (2.7), but that only limits which theories are actually reachable under
 ;; an older configured version, not whether the ALL logic can be set at all.
)


