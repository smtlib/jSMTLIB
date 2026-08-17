; a match expression must have at least one case
(set-logic ALL)
(declare-datatype Color ((red) (green) (blue)))
(declare-fun c () Color)
(assert (match c ()))
