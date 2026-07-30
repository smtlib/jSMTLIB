; declare-datatypes error cases: empty sort list, size mismatch, bad symbol, truncated
(set-logic QF_UF)
(declare-datatypes () (((red) )))
(declare-datatypes ((Color 0) (Shape 0)) (((red) )))
(declare-datatypes ((|.X| 0)) (((red) )))
(declare-datatypes (
