# Security policy

## Reporting a vulnerability

Report vulnerabilities privately through GitHub:
[Report a vulnerability](https://github.com/smtlib/jSMTLIB/security/advisories/new)
(the **Security** tab of this repository). Please do not open a public issue.

You will receive an acknowledgment within 14 days. Fixes are made in the next release, and its release
notes identify the vulnerability fixed.

## Scope

jSMTLIB runs locally, on SMT-LIB input the user chooses, and starts the solver processes the user configures.
A vulnerability is, for example, a way for crafted input (an SMT-LIB script, a solver's output, LSP messages
to the language server) to execute code, read or write files beyond what the user asked for, or exhaust
resources outside jSMTLIB itself.

Running a solver executable is jSMTLIB's purpose: the solver named on the command line or in
`jsmtlib.properties` is trusted. A wrong answer (a solver result misreported, or an unsound translation in
an adapter) is a serious bug but not a vulnerability; report it as an ordinary
[issue](https://github.com/smtlib/jSMTLIB/issues).

Only the latest release is supported.
