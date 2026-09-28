; A FloatingPoint sort's significand width must be greater than 1 (paired with
; err_fpSortEbTooSmall.tst, which is too-small in the other index instead).
(set-logic ALL)
(declare-fun x () (_ FloatingPoint 8 1))
