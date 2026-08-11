; Tests get-assertions and :assertion-stack-levels together, across the initial
; state, various pushes and pops, reset-assertions, and reset.
(set-option :interactive-mode true)
(set-logic QF_UF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
; initial state: no pushed scopes, no assertions
(get-info :assertion-stack-levels)
(get-assertions)
; push one level, assert
(push 1)
(assert a)
(get-info :assertion-stack-levels)
(get-assertions)
; push again (nested), assert
(push 1)
(assert b)
(get-info :assertion-stack-levels)
(get-assertions)
; pop back one level
(pop 1)
(get-info :assertion-stack-levels)
(get-assertions)
; push two levels at once, assert
(push 2)
(assert c)
(get-info :assertion-stack-levels)
(get-assertions)
; pop both levels at once
(pop 2)
(get-info :assertion-stack-levels)
(get-assertions)
; reset-assertions: clears all pushed scopes and assertions, and (for solvers
; where :global-declarations is not enabled/supported) may also clear prior
; declarations, returning to the state right after set-logic -- so a fresh
; symbol (not one declared before reset-assertions) is used here rather than
; reasserting one of a/b/c, whose declared-ness after reset-assertions varies
; by solver.
(reset-assertions)
(get-info :assertion-stack-levels)
(get-assertions)
(declare-fun e () Bool)
(push 1)
(assert e)
(get-info :assertion-stack-levels)
(get-assertions)
; reset: clears everything, including the logic
(reset)
(get-info :assertion-stack-levels)
(set-option :interactive-mode true)
(set-logic QF_UF)
(get-info :assertion-stack-levels)
(get-assertions)
