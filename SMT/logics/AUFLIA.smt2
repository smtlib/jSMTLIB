(logic AUFLIA

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

 :theories (Ints ArraysEx)

 :language 
 "Closed formulas built over arbitrary expansions of the Ints and ArraysEx
  signatures with free sort and function symbols, but with the following 
  restrictions:
  - all terms of sort Int are linear, that is, have no occurrences of the
    function symbols *, **, /, div, mod, and abs, except as specified in the 
    :extensions attributes;
  - all array terms have sort (Array Int Int).
 "

 :extensions
 "As in the logic QF_AUFLIA."

:notes
 "This logic properly extends the logic QF_AUFLIA by allowing quantifiers."
)


