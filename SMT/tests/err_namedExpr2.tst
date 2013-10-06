; tests that named expressions are closed
(set-logic AUFNIRA)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (forall ((r Bool)) (! r :named R))) ; error
(assert (exists ((r Bool)) (! r :named R))) ; error
(assert (forall ((r Bool)) (and r (! q :named R)))) ; OK
(assert (let ((r true)) (! r :named R))) ; error - R already defined
(assert (let ((r true)) (! r :named R2))) ; OK
(assert (forall ((r Bool)) (let ((r true)) (! r :named RR)))) ; OK
(assert (forall ((q Bool)) (let ((r q)) (! r :named RRR)))) ; error - FIXME
