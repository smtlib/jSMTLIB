(set-option :produce-models true)
(set-logic ALL)
(declare-const yyy Bool)

; quantifiers and patterns
(declare-sort S 0)
(declare-fun le (S S) Bool)
(declare-fun zz () S)
(assert (forall ((x S)(y S)(z S)) (=> (and (le x y)(le y z)) (le x z))))
(assert (exists ((x S)(y S)(z S)) (=> (and (le x y)(le y z)) (le x z))))
(assert (forall ((x S)(y S)(z S)) (! (=> (and (le x y)(le y z)) (le x z))  :pattern ((le x zz)) :pattern ((le y zz) (le zz z)) )))
