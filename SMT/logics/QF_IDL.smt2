(logic QF_IDL

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli"
 :date "2010-04-30"

 :theories (Ints)

 :language
 "Closed quantifier-free formulas with atoms of the form:
  - p
  - (op (- x y) n),
  - (op (- x y) (- n)),
  - (op x y), or
  where
    - p is a variable or free constant symbol of sort Bool,
    - op is <, <=, >, >=, =, or distinct,
    - x, y are free constant symbols of sort Ints, 
    - n is a numeral. 
 "
)


