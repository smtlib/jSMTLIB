; Issue #59: Solver_z3_recent.parseResponse() rewrites a "line N" reference in an error
; response to compensate for linesOffset (the extra print-success priming line jSMTLIB sends
; before the user's script) -- but must scope that rewrite to responses that actually carry an
; (error ...), never to a coincidental "line N" substring elsewhere (e.g. inside a returned
; string literal). The first block below forces a genuine z3-side error (an undeclared
; function jSMTLIB's own client-side checker does not itself catch) at a known script line, to
; confirm the reported line number matches the *script's* line, not z3's own (offset) view of
; it. The second block returns a string value containing literal "line N" text that must
; survive untouched.
(set-logic QF_LIA)
(declare-const x Int)
(assert (undeclaredfun x))
(check-sat)
(reset)
(set-logic ALL)
(set-option :produce-models true)
(declare-const s String)
(assert (= s "line 5 of the report"))
(check-sat)
(get-value (s))
