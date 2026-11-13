; The value of each QF_BV operator (FixedSizeBitVectors and the QF_BV extensions), each
; checked on its own: every check-sat is unsat. #b1100 is 12 unsigned, -4 signed; #b1010 is 10, -6.
(set-logic QF_BV)
(push 1)
(assert (not (= (concat #b1100 #b1010) #b11001010)))  ; concat
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ extract 2 1) #b1100) #b10)))  ; extract
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvnot #b1100) #b0011)))  ; bvnot
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvand #b1100 #b1010) #b1000)))  ; bvand
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvor #b1100 #b1010) #b1110)))  ; bvor
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvneg #b1100) #b0100)))  ; bvneg
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvadd #b1100 #b1010) #b0110)))  ; bvadd
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvmul #b1100 #b1010) #b1000)))  ; bvmul
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvudiv #b1100 #b1010) #b0001)))  ; bvudiv
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvudiv #b1100 #b0000) #b1111)))  ; bvudiv by 0
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvurem #b1100 #b1010) #b0010)))  ; bvurem
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvurem #b1100 #b0000) #b1100)))  ; bvurem by 0
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvshl #b1100 #b0001) #b1000)))  ; bvshl
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvlshr #b1100 #b0001) #b0110)))  ; bvlshr
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvult #b1010 #b1100) true)))  ; bvult
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvnand #b1100 #b1010) #b0111)))  ; bvnand
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvnor #b1100 #b1010) #b0001)))  ; bvnor
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvxor #b1100 #b1010) #b0110)))  ; bvxor
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvxnor #b1100 #b1010) #b1001)))  ; bvxnor
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvcomp #b1100 #b1010) #b0)))  ; bvcomp
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsub #b1010 #b1100) #b1110)))  ; bvsub
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsdiv #b1010 #b0011) #b1110)))  ; bvsdiv
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsrem #b1011 #b0011) #b1110)))  ; bvsrem
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsmod #b1011 #b0011) #b0001)))  ; bvsmod
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvashr #b1100 #b0001) #b1110)))  ; bvashr
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ repeat 2) #b10) #b1010)))  ; repeat
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ zero_extend 2) #b11) #b0011)))  ; zero_extend
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ sign_extend 2) #b10) #b1110)))  ; sign_extend
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ rotate_left 1) #b1001) #b0011)))  ; rotate_left
(check-sat)
(pop 1)
(push 1)
(assert (not (= ((_ rotate_right 1) #b1001) #b1100)))  ; rotate_right
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvule #b1100 #b1100) true)))  ; bvule
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvugt #b1100 #b1010) true)))  ; bvugt
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvuge #b1100 #b1010) true)))  ; bvuge
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvslt #b1010 #b1100) true)))  ; bvslt
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsle #b1010 #b1100) true)))  ; bvsle
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsgt #b1100 #b1010) true)))  ; bvsgt
(check-sat)
(pop 1)
(push 1)
(assert (not (= (bvsge #b1100 #b1010) true)))  ; bvsge
(check-sat)
(pop 1)
(push 1)
(assert (not (= (_ bv12 4) #xc)))  ; (_ bvX n)
(check-sat)
(pop 1)
