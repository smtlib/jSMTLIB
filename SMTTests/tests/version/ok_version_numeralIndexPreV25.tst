; A purely numeral-indexed identifier (unlike err_version_symbolIndex.tst's symbol
; index) is allowed even before SMT-LIB V2.5, since the "symbol indices need V2.5"
; restriction only concerns indices that are themselves symbols, not numerals.
(set-info :smt-lib-version 2.0)
(set-logic QF_BV)
(declare-fun b () (_ BitVec 4))
(assert (= b #b0000))
(check-sat)
