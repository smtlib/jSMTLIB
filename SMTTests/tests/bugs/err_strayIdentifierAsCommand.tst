; Issue #121: a bare, non-parenthesized token at the top level used to be silently
; swallowed while the parser hunted for the next '(' -- interactively this looked like
; a hang (nothing was ever printed unless --verbose was on), and in a file it could
; silently discard everything after it if no further '(' ever appeared. Now reports a
; real, visible error immediately.
(set-logic QF_UF)
x
