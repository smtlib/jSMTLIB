; OPTIONS: --relax
; With --relax a :named term may refer to a let-bound variable whose value is closed, with a warning;
; one whose value refers to a quantified variable is still an error (#227)
(set-logic ALL)
(declare-sort U 0)
(assert (let ((y true)) (! (and y y) :named b)))
(assert (forall ((q U)) (let ((r q)) (! (= r r) :named e))))
