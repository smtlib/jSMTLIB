; parametric datatypes: constructors and selectors instantiate at each use, and a nullary
; constructor takes its sort from an as qualifier (#168)
(set-logic ALL)
(declare-datatypes ((Lst 1)) ((par (E) ((nil) (cons (hd E) (tl (Lst E)))))))
(declare-datatype Pair (par (X Y) ((mk-pair (fst X) (snd Y)))))
(declare-fun l () (Lst Int))
(declare-fun b () (Lst Bool))
(assert (= l (cons 1 (as nil (Lst Int)))))
(assert (= (hd l) 1))
(assert (= (tl l) (as nil (Lst Int))))
(assert (hd (cons true b)))
(assert (= (fst (mk-pair 1 true)) (hd l)))
(assert (snd (mk-pair l true)))
; Solver bugs (.bad goldens): z3-4.7.1 and z3-4.8.12 reject the parametric constructor mk-pair
; applied to arguments; smtinterpol-2.5 rejects the same terms ("Application of function null").
