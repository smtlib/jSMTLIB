; Issue #38: (check-sat-assuming ()) -- a syntactically legal, zero-assumption
; check-sat-assuming, equivalent to a plain check-sat -- must be accepted, not rejected with
; "Expected a parenthesized list of at least one term."
(set-logic QF_UF)
(assert true)
(check-sat-assuming ())
(declare-const b Bool)
(check-sat-assuming (b))
