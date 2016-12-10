; check that patterns are typechecked
(set-logic UFLIA )
(declare-fun le (Int Int) Bool)
(declare-fun zz () Int)
(assert (forall ((x Int)(y Int)(z Int)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le x true))  )))
(assert (forall ((x Int)(y Int)(z Int)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le yy yy))  )))
