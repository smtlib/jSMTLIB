; a match pattern must use a known constructor of the scrutinee's datatype
(set-logic ALL)
(declare-datatype Color ((red) (green) (blue)))
(declare-fun c () Color)
(assert (match c ( ((unknown x y) true) )))
