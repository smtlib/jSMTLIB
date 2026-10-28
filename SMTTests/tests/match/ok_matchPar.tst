; match on a parametric datatype: pattern variables take the instantiated selector sorts,
; and a nullary constructor pattern is recognized, so the match is exhaustive (#168)
(set-logic ALL)
(declare-datatypes ((Lst 1)) ((par (E) ((nil) (cons (hd E) (tl (Lst E)))))))
(declare-fun l () (Lst Int))
(assert (match l ((nil false) ((cons h t) (and (= h 1) (= t (as nil (Lst Int))))))))
; Solver bug (.bad golden): smtinterpol-2.5 crashes on the match over a parametric datatype.
