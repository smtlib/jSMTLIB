(set-logic AUFLIA)
(assert (exists ((x Int)) (and (<= 1 x)(<= x 3))))
(check-sat)
