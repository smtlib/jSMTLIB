; a quantifier pattern is typechecked like any other term
(set-logic AUFLIA)
(declare-fun le (Int Int) Bool)
(assert (forall ((x Int)(y Int)(z Int)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le x true))  )))
