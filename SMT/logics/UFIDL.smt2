(logic UFIDL

 :smt-lib-version 2.0
 :written_by "David Cok, from QF_UFIDL"
 :date "2015-06-27"

 :theories (Ints)


 :language
 "Closed formulas built over an arbitrary expansion with 
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


