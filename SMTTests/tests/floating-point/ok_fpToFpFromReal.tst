; (_ to_fp eb sb) overload (c): RoundingMode + Real -- convert from Real. 4.0 is exact
; in binary32.
(set-logic ALL)
(assert (= ((_ to_fp 8 24) RNE 4.0) (fp.add RNE ((_ to_fp 8 24) RNE 2.0) ((_ to_fp 8 24) RNE 2.0))))
(check-sat)
