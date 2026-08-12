; a :named symbol that fails the closedness check must not be registered
(set-logic AUFNIRA)
(declare-fun q () Bool)
(assert (forall ((r Bool)) (! r :named R)))
(assert (forall ((r Bool)) (and r (! q :named R))))
