; EOF inside the term list of a :pattern
(set-logic ALL)
(declare-fun f (Bool) Bool)
(assert (forall ((x Bool)) (! (f x) :pattern ((f x) 