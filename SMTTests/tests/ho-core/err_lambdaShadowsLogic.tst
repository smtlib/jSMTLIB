; lambda's variables may not shadow a function symbol of the logic (Remark 7)
(set-logic ALL)
(declare-const k (-> Int Bool))
(assert (= k (lambda ((ite Int)) (> ite 0))))
