; (_ FloatingPoint eb sb) resolves; two declarations at the same (eb,sb) are the same sort.
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 24))
(declare-fun y () (_ FloatingPoint 8 24))
(assert (= x y))
(check-sat)
