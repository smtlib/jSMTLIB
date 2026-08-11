; Tests that get-assertions lists assertions in the order they were asserted,
; not e.g. declaration order or some other internal ordering -- both within a
; single scope and across a push boundary.
(set-option :interactive-mode true)
(set-logic QF_UF)
(declare-fun z () Bool)
(declare-fun a () Bool)
(declare-fun m () Bool)
(declare-fun q () Bool)
; assert out of declaration/alphabetical order within the base scope
(assert z)
(assert a)
(assert m)
(get-assertions)
; push, then assert more (including a repeat of an earlier symbol) -- the
; base-scope assertions must still come first, in their original order, with
; the newly-pushed assertions appended after, also in their assert order
(push 1)
(assert q)
(assert (not z))
(get-assertions)
