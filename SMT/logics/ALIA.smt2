(logic ALIA

 :smt-lib-version 2.0
 :written_by "David Cok, from QF_ALIA"
 :date "2015-06-27"

 :theories (Ints ArraysEx)

 :language 
 "Closed formulas built over arbitrary expansions of the
  Ints and ArraysEx signatures with free constant symbols, but
  with the following restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, /, div, mod, and abs, except as specified in the 
    :extensions attributes;
  - all array terms have sort (Array Int Int).
 "

 :extensions
 "As in the logic QF_LIA."
)

