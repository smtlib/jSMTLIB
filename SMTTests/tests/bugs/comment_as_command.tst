; OPTIONS: --echo
; Issue #42 point 1: a comment is now modeled as its own synthetic C_comment pseudo-command,
; interleaved into the parsed command stream, so it is forwarded to the solver (and, under
; --echo, printed back) uniformly for any command that follows it -- not just the handful of
; command classes that used to have their own ad hoc prefixText forwarding.
;
; Four checks combined into one session: a comment immediately before an ordinary command is
; echoed as its own line; a comment between a command's own arguments is ignored (the command
; still executes normally, with no comment in its echoed reconstruction); a real multi-line
; comment (each line already carrying its own ';') echoes back verbatim with no extra ';'
; characters injected; and plain blank lines between commands (no actual comment) do not
; spuriously become their own (empty) comment commands.
;
; Two of the original bug's sub-cases are not exercised here (and stay covered by
; CommentAsCommandBugTest, a remaining JUnit test): a trailing comment at true end-of-script
; never actually reaches the driver's own command loop, and a C_comment built directly via its
; public Java constructor (rather than parsed from real script text) is only reachable via
; direct API use.
;
; The bare .out golden is real-solver output (a real solver can determine this trivial
; QF_UF problem is definitely sat); Solver_test's own less-informative "unknown" answers
; are captured separately in .out.test.
(set-logic QF_UF)
; hello
(check-sat)
(assert ; mid-comment
 true)
; line one
; line two
(check-sat)


(check-sat)
