; a symbol resembling z3's old bit-vector literal syntax (bvVALUE[WIDTH]) comes back unchanged
(set-option :produce-models true)
(set-logic QF_UF)
(declare-fun |bv1[2]| () Bool)
(assert |bv1[2]|)
(check-sat)
(get-value (|bv1[2]|))
