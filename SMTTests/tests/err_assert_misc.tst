; miscellaneous assert-level TypeChecker errors:
; _ wildcard outside match, string literal without STRING theory
(set-logic QF_UF)
(assert _)
(assert "hello")
