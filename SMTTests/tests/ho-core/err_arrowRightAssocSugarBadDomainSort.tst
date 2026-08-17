; -> :right-assoc sugar (more than 2 arguments) still propagates a sort error from
; one of its argument sorts -- distinct from err_arrowBadDomainSort.tst, which uses
; the base 2-argument form
(set-logic ALL)
(declare-fun f () (-> BadSort Int Int Bool))
