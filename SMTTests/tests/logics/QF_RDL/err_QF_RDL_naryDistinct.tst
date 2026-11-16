; QF_RDL: an atom must be binary; (distinct x y z) is not a QF_RDL atom
(set-logic QF_RDL)
(declare-const x Real)
(declare-const y Real)
(declare-const z Real)
(assert (distinct x y z))
