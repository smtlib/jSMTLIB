; Issue #48: confirms QF_NIA/UFNIA correctly forbid the exponentiation operator ** (per their
; own :language text), that UFNIA's new explicit checkFcnDeclaration override still permits
; uninterpreted functions, and that QF_EIA (the "QF_NIA but ** permitted" variant) still
; accepts it.
(set-logic QF_NIA)
(declare-const x Int)
(assert (= (** x 2) 4))
(reset)
(set-logic UFNIA)
(declare-const x Int)
(assert (= (** x 2) 4))
(reset)
(set-logic UFNIA)
(declare-fun f (Int) Int)
(reset)
(set-logic QF_EIA)
(declare-const x Int)
(assert (= (** x 2) 4))
