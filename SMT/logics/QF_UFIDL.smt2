(logic QF_UFIDL

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli"
 :date "2010-05-12"

 :theories (Ints)


 :language
 "Closed quantifier-free formulas built over an arbitrary expansion with 
  free sort and function symbols of the signature consisting of 
  - all the sort and function symbols of Core and
  - the following symbols of Int:

    :sorts ((Int 0))
    :funs ((NUMERAL Int) 
           (- Int Int Int)
           (+ Int Int Int) 
           (<= Int Int Bool)
           (< Int Int Bool)
           (>= Int Int Bool)
           (> Int Int Bool)
          )

  Additionally, for every term of the form (op t1 t2) with op in {+, -}, 
  at least one of t1 and t2 is a numeral. 
 "
)


