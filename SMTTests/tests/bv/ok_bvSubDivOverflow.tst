; QF_BV overflow predicates added in 2023: bvusubo, bvssubo, bvsdivo.
; 0-1 underflows unsigned; -8-1 and -8/-1 overflow signed 4-bit; the others do not.
(set-logic QF_BV)
(declare-fun s () (_ BitVec 4))
(declare-fun t () (_ BitVec 4))
(push 1)
(assert (bvusubo s t))
(assert (bvssubo s t))
(check-sat)  ; sat: s = #x0, t = #x8
(assert (bvsdivo s t))
(check-sat)  ; unsat: bvsdivo needs s = #x8, t = #xf, and -8 - -1 does not overflow
(pop 1)
(push 1)
(assert (not (and (bvusubo #x0 #x1) (not (bvusubo #x1 #x0))
                  (bvssubo #x8 #x1) (not (bvssubo #x7 #x1))
                  (bvsdivo #x8 #xf) (not (bvsdivo #x8 #x1)))))
(check-sat)  ; unsat
(pop 1)
