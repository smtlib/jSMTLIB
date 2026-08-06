; declare-datatypes: recursive datatype appears nested inside another sort constructor in a selector
(set-logic QF_UF)
(declare-datatypes ((Color 0)) (((red) (green (shades (Array Int Color))))))
