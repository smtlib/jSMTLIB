; match on datatypes whose sort name is written with bars, at declaration or at use
(set-logic ALL)
(declare-datatype |My List| ((nil) (cons (hd Int) (tl |My List|))))
(declare-datatype L ((a) (b)))
(declare-fun x () |My List|)
(declare-fun y () |L|)
(assert (match x ((nil true) ((cons h t) false))))
(assert (match y ((a true) (b false))))
