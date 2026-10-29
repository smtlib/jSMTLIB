; A hexadecimal index parses (the Strings theory's (_ char H) needs it), but bit-vector identifiers take numerals
(set-logic QF_BV)
(declare-fun x () (_ BitVec #x8))
(declare-fun y () (_ BitVec 8))
(assert (= #x0 ((_ extract #x3 0) y)))
(assert (= (_ bv1 #x8) y))
(assert (= y ((_ repeat #x1) y)))
