; QF_RDL forbids quantifiers, UF, and new sorts
(set-logic QF_RDL)
(declare-const x Real)
(assert (forall ((z Real)) (>= z 0.0)))
(declare-fun f (Real) Real)
(declare-sort Tag 0)
