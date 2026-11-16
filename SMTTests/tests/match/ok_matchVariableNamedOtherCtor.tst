; A match pattern named for a constructor of another par datatype is a variable
(set-logic ALL)
(declare-datatypes ((L 1) (M 1)) ((par (A) ((nil) (cons (hd A) (tl (L A)))))
                                  (par (B) ((none) (some (val B))))))
(declare-const m (M Int))
(assert (= 0 (match m ((nil 0) ((some v) v)))))
