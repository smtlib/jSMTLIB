; tests illegal uses of as identifiers
(set-logic AUFLIRA)
(assert (= ((as + Int) 4 3) 1)) ;; unneeded disambiguation
(assert (= ((as and Bool) true false) false)) ;; not overloaded
(assert (= ((as zzz Bool) true false) false)) ;; unknown identifier
(declare-sort S 0)
(assert (= ((as + S) 4 3) 1))  ;; not overloaded to S
