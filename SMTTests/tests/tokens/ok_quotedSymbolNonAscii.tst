; Quoted symbols may contain characters 128 and beyond (SMT-LIB 2.5+);
; they reach the solver unchanged, and get-value's response is parsed and printed back with bars.
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun |café| () Bool)
(declare-fun |x ∀ π| () Bool)
(assert (and |café| (not |x ∀ π|)))
(check-sat)
(get-value (|café| |x ∀ π|))
