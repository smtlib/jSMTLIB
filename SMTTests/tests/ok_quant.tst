; quantifiers and patterns
(set-logic UFLIA)
(declare-fun le (Int Int) Bool)
(declare-fun zz () Int)
(assert (forall ((x Int)(y Int)(z Int)) (=> (and (le x y)(le y z)) (le x z))))
(assert (exists ((x Int)(y Int)(z Int)) (=> (and (le x y)(le y z)) (le x z))))
(assert (forall ((x Int)(y Int)(z Int)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le x zz)) :pattern ((le y zz) (le zz z)) )))
