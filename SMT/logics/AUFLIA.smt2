(logic AUFLIA

 :smt-lib-version 2.0
 :written_by "Cesare Tinelli"
 :date "2010-04-30"

 :theories (Ints ArraysEx)

 :language 
 "Closed formulas built over arbitrary expansions of the Ints and ArraysEx
  signatures with free sort and function symbols, but with the following 
  restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, /, div, mod, and abs, except as specified in the 
    :extensions attributes;
  - all array terms have sort (Array Int Int).
 "

 :extensions
 "As in the logic QF_AUFLIA."

:notes
 "This logic properly extends the logic QF_AUFLIA by allowing quantifiers."

)


