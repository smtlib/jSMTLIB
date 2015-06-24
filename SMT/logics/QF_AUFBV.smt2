(logic QF_AUFBV

:smt-lib-version 2.0
:written_by "Cesare Tinelli and Clark Barrett"
:date "2010-05-11"

:theories (Fixed_Size_BitVectors ArraysEx)

:language 
 "Closed quantifier-free formulas built over an arbitrary expansion of the
  Fixed_Size_BitVectors and ArraysEx signatures with free sort and function
  symbols, but with the restriction that all array terms have sort of the 
  form (Array (_ BitVec i) (_ BitVec j)) for some i, j > 0.
 "

:extensions
 "As in the logic QF_BV."
)


