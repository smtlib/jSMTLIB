; An ill-sorted third assumption: the error's column is that of the check-sat-assuming text, also
; for z3 4.3 and 4.5, which get it as a padded legacy check-sat
(set-logic QF_UF)
(declare-sort X 0)
(declare-fun x () X)
(declare-fun p () Bool)
(declare-fun q () Bool)
(check-sat-assuming (p (not q) x))
