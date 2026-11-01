; QF_AX: quantifier-free arrays with free sort symbols; no UF with arguments
(set-logic QF_AX)
(declare-sort A 0)
(declare-const a (Array A A))
(declare-const x A)
(assert (= (select a x) x))
