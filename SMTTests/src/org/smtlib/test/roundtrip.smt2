; SMT-LIB round-trip test.  Each non-comment line is a command whose
; write() output must exactly reproduce the input text.
; Covers all command write() methods and their branches (0-element vs
; 1+-element loops, attribute with/without value, etc.).

; assert: exercises IFcnExpr (0,1,2+ args), IForall/IExists (1 and 2 decls),
;         ILet (1 binding), IAttributedExpr (:named attribute), IDeclaration,
;         IBinding, IAttribute with value, ISymbol
(assert true)
(assert (not true))
(assert (and true false))
(assert (or true false true))
(assert (forall ((x Bool) ) x))
(assert (forall ((x Bool) (y Bool) ) (and x y)))
(assert (exists ((x Bool) ) x))
(assert (let ((z true) ) z))
(assert (! true :named myassertion))

; check-sat family: 1 and 2 elements in the assumption list
; (parseListTerms rejects empty lists, so 0-element write() branch is unreachable)
(check-sat)
(check-sat-assuming ( p))
(check-sat-assuming ( p q))

; declare-const and declare-fun: 0, 1, and 2 argument sorts
(declare-const c Bool)
(declare-fun f () Bool)
(declare-fun g (Bool ) Bool)
(declare-fun h (Int Bool ) Int)

; declare-datatype: non-parametric (symbols null) and parametric (symbols non-null)
; Note: datatype body uses trailing space before ')' per printer convention
(declare-datatype Color ((red) (green) (blue) ))
(declare-datatype Option ( par (A ) ((some (val A)) (none) ) ))

; declare-datatypes: parallel sort-decl and datatype lists (space after '(' per printer)
(declare-datatypes ( (Color 0)) ( ((red) (green) (blue) )))

; declare-sort: arity 0 and arity > 0
(declare-sort MySort 0)
(declare-sort MySort2 2)

; declare-sort-parameter: single symbol argument
(declare-sort-parameter A)

; define-const: syntactic sugar for define-fun with no parameters
(define-const x Bool true)

; define-fun: 0 and 2 parameters
(define-fun f0 () Bool true)
(define-fun f1 ((p Bool)(q Bool)) Bool (and p q))

; define-fun-rec: 1 parameter (same write format as define-fun)
(define-fun-rec f2 ((x Bool)) Bool (not x))

; define-funs-rec: two parallel lists (decl list and body list, each with trailing space)
(define-funs-rec ((f () Bool) ) (true ))

; define-sort: 0 and 1 sort parameters (note trailing space inside paren)
(define-sort MyAlias () Bool)
(define-sort MySub (B ) Bool)

; echo: exercises IStringLiteral via arg.toString()
(echo "hello")

; simple zero-argument commands
(exit)
(get-assertions)
(get-assignment)
(get-model)
(get-proof)
(get-unsat-assumptions)
(get-unsat-core)
(reset)
(reset-assertions)

; commands with a keyword argument
(get-info :status)
(get-option :print-success)

; get-value: 1 and 2 expressions (note leading space inside paren)
(get-value ( x))
(get-value ( x y))

; push/pop: numeral argument
(pop 1)
(push 2)

; set-info: keyword + symbol value, and keyword + string-literal value
(set-info :status sat)
(set-info :author "Alice")

; set-logic and set-option
(set-logic QF_UF)
(set-option :print-success true)

; IDecimal, IBinaryLiteral, IHexLiteral: literal expressions in assert
(assert 1.5)
(assert #b00001010)
(assert #x0a)

; IMatch, IMatchCase, IPattern: bare constructor patterns and constructor-with-params patterns
(assert (match c ( (red true) (blue false))))
(assert (match c ( ((cons h t) h) (nil 0))))

; ISexpr.ISeq: s-expression sequence as a set-info attribute value
(set-info :x ( a b c ))

; trailing comment to verify EOF handling
