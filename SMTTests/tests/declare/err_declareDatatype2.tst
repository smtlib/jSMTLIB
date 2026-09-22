; declaring an already declared datatype sort
(set-logic ALL)
(declare-datatype Color ((red) (green) (blue)))
(push 1)
(declare-datatype Color ((red) (green) (blue)))
