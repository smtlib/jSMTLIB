(logic QF_RDL

 :smt-lib-version 2.7
 :smt-lib-release "2024-07-21"
 :written-by "Cesare Tinelli"
 :date "2010-04-30"
 :last-updated "2024-07-21"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2024-07-21 Updated to Version 2.7.
  2015-04-25 Updated to Version 2.5.
  2010-12-16 Replaced erroneous ''n > 0'' with ''n > 1'' in language attribute.
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


