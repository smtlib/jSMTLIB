; The index of (_ char H) is at most #x2FFFF
(set-logic ALL)
(assert (= "A" (_ char #x30000)))
(assert (= "A" (_ char #x2FFFF)))
