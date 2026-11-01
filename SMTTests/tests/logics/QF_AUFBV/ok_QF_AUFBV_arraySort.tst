; QF_AUFBV: array sorts of the form (Array (_ BitVec i) (_ BitVec j)), also through abbreviations
(set-logic QF_AUFBV)
(define-sort W () (_ BitVec 8))
(define-sort P (X) (Array X X))
(declare-const a (Array W (_ BitVec 16)))
(declare-const p (P W))
(declare-fun f ((Array (_ BitVec 4) W)) Bool)
(define-fun d ((x (P (_ BitVec 2)))) Bool true)
(assert (= (select a #x00) #x0000))
