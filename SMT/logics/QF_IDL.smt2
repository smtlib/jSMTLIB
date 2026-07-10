(logic QF_IDL

 :smt-lib-version 2.7
 :smt-lib-release "2024-07-21"
 :written-by "Cesare Tinelli"
 :date "2010-04-30"
 :last-updated "2024-07-21"
 :update-history
 "Note: history only accounts for content changes, not release changes.
  2024-07-21 Updated to Version 2.7.
  2015-04-25 Updated to Version 2.5.
 "

 :theories ( Ints )

 :language
 "Closed quantifier-free formulas with atoms of the form:
  - q
  - (op (- x y) n),
  - (op (- x y) (- n)), or
  - (op x y)
  where
    - q is a variable or free constant symbol of sort Bool,
    - op is <, <=, >, >=, =, or distinct,
    - x, y are free constant symbols of sort Int, 
    - n is a numeral. 
 "
)


