; a :named symbol inside a let must not conflict with a previously used name
(set-logic AUFNIRA)
(declare-fun q () Bool)
(assert (forall ((r Bool)) (and r (! q :named R))))
(assert (let ((r true)) (! r :named R)))
