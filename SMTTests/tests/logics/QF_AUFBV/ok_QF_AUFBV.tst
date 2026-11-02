; QF_AUFBV: quantifier-free bitvectors + arrays + UF
(set-logic QF_AUFBV)
(declare-const x (_ BitVec 8))
(declare-const a (Array (_ BitVec 8) (_ BitVec 8)))
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
(assert (= x (f #x00)))
(assert (= x (select a #x00)))
