; Issue #89: QF_FP.smt2 (a jSMTLIB-invented convenience logic) had no matching
; org.smtlib.logic.QF_FP restriction class, so its own :language ("closed quantifier-free
; formulas ... with free constant symbols") was not enforced at all -- a quantifier and a
; declared function both silently succeeded. Fixed by adding QF_FP.java with the same
; noQuantifiers/noFunctions/noSorts restrictions every sibling logic already has.
(set-logic QF_FP)
(assert (forall ((x Real)) (= x x)))
(reset)
(set-logic QF_FP)
(declare-fun f (Real) Real)
(reset)
(set-logic QF_FP)
(declare-sort S 0)
(reset)
(set-logic QF_FP)
(declare-const r Real)
(declare-const bv (_ BitVec 8))
(declare-const f (_ FloatingPoint 8 24))
