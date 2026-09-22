; A plain SMT-LIB identifier that happens to collide with one of Solver_simplify's own
; *internal* reserved connective/keyword names (its private `reservedWords` set: AND, OR,
; NOT, EQ, NEQ, LBL, PATS, ...) is perfectly legal SMT-LIB syntax -- SMT-LIB's own
; reserved-word set is a much smaller, lowercase-with-hyphens set (see
; tests/reserved-words/), and every solver here accepts an uppercase "AND"/"EQ" as an
; ordinary symbol. No existing test used a name from Simplify's specific reserved-word
; set, so Solver_simplify.Translator.visit(ISymbol)'s escaping branch (renaming the
; colliding translated name to "<name>?!" before wrapping it in |...| bars, so it can't
; collide with Simplify's own AND/EQ keywords on the wire) was never exercised.
;
; NOTE (simplify golden): this exercises an internal wire-protocol detail that is
; invisible in jSMTLIB's own response text (declare-fun/assert only ever report
; "success" regardless of how the name was escaped) -- the only real-Simplify-specific
; risk is check-sat silently getting the wrong answer if the escaping were ever broken.
; No simplify binary is available on this machine to capture or verify simplify's actual
; output; a real golden (tests/declare/ok_declareFunSimplifyReservedWordCollision.tst.out.simplify,
; expected to be identical to the bare golden below if the escaping works as read) still
; needs to be captured against a real Simplify process, e.g. in CI.
(set-logic QF_UF)
(declare-fun AND () Bool)
(declare-fun EQ () Bool)
(assert (= AND EQ))
(check-sat)
