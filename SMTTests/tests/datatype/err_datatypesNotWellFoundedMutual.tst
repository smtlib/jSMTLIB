; declare-datatypes: mutually recursive datatypes with no base case; each error is positioned
; at the datatype's name.
(set-logic ALL)
(declare-datatypes ((A 0) (B 0)) (((a (ab B))) ((b (ba A)))))
