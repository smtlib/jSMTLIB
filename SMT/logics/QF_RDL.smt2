(logic QF_RDL

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli"
 :date "2010-04-30"

 :updated "2010-12-16"
 :update_log 
 "2010-12-16 Replaced erroneous ''n > 0'' with ''n > 1'' in language attribute.
 "

 :theories (Reals)

 :language 
 "Closed quantifier-free formulas with atoms of the form:
  - p
  - (op (- x y) c),
  - (op x y),
  - (op (- (+ x ... x) (+ y ... y)) c) with n > 1 occurrences of x and of y,
  where
    - p is a variable or free constant symbol of sort Bool,
    - c is an expression of the form m or (- m) for some numeral m,
    - op is <, <=, >, >=, =, or distinct,
    - x, y are free constant symbols of sort Real. 
  "

 :extensions
 "The expression (op (- x y) (/ c n)) where n is a numeral other than 0 and
  c is an expression of the form m or (- m) for some numeral m, 
  abbreviates the expression
  (op (- (+ x ... x) (+ y ... y)) c) with n occurrences of x and y.
 "
)


