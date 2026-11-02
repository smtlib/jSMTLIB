; parametric datatypes: an instantiation must be consistent across a constructor's
; arguments, and a bare nullary constructor has no sort to take (#168)
(set-logic ALL)
(declare-datatypes ((Lst 1)) ((par (E) ((nil) (cons (hd E) (tl (Lst E)))))))
(declare-fun l () (Lst Int))
(assert (= l (cons true (as nil (Lst Int)))))
(assert (= (hd l) true))
(assert (= l (as nil (Lst Bool))))
(assert (= l nil))
