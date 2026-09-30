#!/usr/bin/env python3
"""Probe each configured SMT solver for which named SMT-LIB logics it accepts
via (set-logic L), for every logic other than ALL (ALL's own internal
capabilities are covered separately by ALL-logic-report.py), and emit a
GitHub-flavored markdown table -- Logics.md.

The logic list isn't hardcoded: it's read straight from jSMTLIB's own logic
definitions under SMT/logics/ at run time, so it can't go stale.
  - "Current" rows are every `(logic ...)` file directly under SMT/logics/
    (the current, SMT-LIB-2.7-era set; the `(theory ...)` files there --
    Core, ArraysEx, Reals_Ints, etc. -- are theory definitions, not logics,
    and aren't valid set-logic arguments, so they're skipped).
  - "V2.0" rows are logic names found only under SMT/logics/V2.0/ and not
    already covered by a "Current" row -- logics that existed in the
    SMT-LIB 2.0 logic set but have since been renamed, folded into a newer
    logic, or dropped (e.g. ALIA, BV, NIA, NRA, UF, UFBV). A footnote on
    the group label explains this; it isn't repeated in every row.

Each row is a minimal two-command script:
  (set-option :print-success true)
  (set-logic L)
and the grade is purely "did the solver's response to set-logic say
success" -- not whether it can actually do anything useful in that logic.
(That's a different question, answered for ALL by ALL-logic-report.py's
capability probes; this script only checks whether the *name* is
recognized.)

"V2.0" rows are preceded by (set-info :smt-lib-version 2.0) -- per the
SMT-LIB spec this attribute may only be set as the very first command of a
script, so it goes before even :print-success -- to declare the script as
targeting that older logic set, the way a real SMT-LIB 2.0 script would.

Every probe here runs directly against the raw solver binary
(subprocess.run on e.g. z3-4.16.0 with the .smt2 file as its argument) --
jSMTLIB itself is never invoked, so nothing about jSMTLIB's own set-logic
handling or logic-path resolution is being tested.

Grading:
  Y (yes)     - solver responded `success`.
  ~ (partial) - timed out, or produced an ambiguous/unparseable response.
  N (no)      - explicit `unsupported`, an `(error ...)` response, or no
                output at all.

Usage:
  python3 logics-report.py [--solver-dir DIR] [--solvers NAME[,NAME...]]
                            [--logics-dir DIR] [--timeout SECONDS] [--out FILE]
"""

from __future__ import annotations

import argparse
import json
import os
import platform
import re
import subprocess
import sys
import tempfile
import unicodedata
from dataclasses import dataclass
from pathlib import Path

# ---------------------------------------------------------------------------
# Solver discovery (mirrors ALL-logic-report.py/options-report.py; kept
# standalone/duplicated so each script in this folder can be run
# independently)
# ---------------------------------------------------------------------------

SOLVER_FAMILIES = {
    "z3": ("z3-", False),
    "cvc5": ("cvc5-", False),
    "yices2": ("yices2-", False),
    "bitwuzla": ("bitwuzla-", False),
    "alt-ergo": ("alt-ergo-", False),
    "smtinterpol": ("smtinterpol-", True),
}

SOLVER_EXTRA_ARGS = {
    "cvc5": ["--quiet"],
    # Alt-Ergo's native input language is its own, not SMT-LIB: without these it
    # parses an .smt2 file with the wrong front end and answers `unsupported` to
    # every command, which reads as "supports no logic at all". Same flags
    # jSMTLIB's own Solver_altergo adapter uses.
    "alt-ergo": ["--input", "smtlib2", "--output", "smtlib2"],
}


def default_solver_dir() -> Path:
    system = platform.system().lower()
    machine = platform.machine().lower()
    if system == "darwin":
        p = "macos"
    elif system == "linux":
        p = "linux"
    elif system.startswith(("mingw", "msys", "cygwin", "windows")):
        p = "windows"
    else:
        p = system
    if machine in ("x86_64", "amd64", "i686"):
        a = "x64"
    elif machine in ("arm64", "aarch64"):
        a = "arm64"
    else:
        a = machine
    subdir = {
        ("macos", "x64"): "Solvers-macos",
        ("macos", "arm64"): "Solvers-macos-arm64",
        ("linux", "x64"): "Solvers-linux",
        ("linux", "arm64"): "Solvers-linux-arm64",
    }.get((p, a), "Solvers-windows" if p == "windows" else f"Solvers-{p}")
    here = Path(__file__).resolve().parent  # SMTTests/reports/
    return here.parent.parent.parent / "OpenJML21" / "Solvers" / subdir


def default_logics_dir() -> Path:
    here = Path(__file__).resolve().parent  # SMTTests/reports/
    return here.parent.parent / "SMT" / "logics"


def _version_key(name: str):
    return [int(n) for n in re.findall(r"\d+", name)]


def discover_solver_instances(solver_dir: Path, wanted=None) -> dict[str, list[tuple[str, Path, bool]]]:
    """Every matching binary for each solver family in solver_dir -- not just
    the newest -- as {family: [(version, path, is_jar), ...]} sorted oldest
    to newest."""
    found: dict[str, list[tuple[list[int], str, Path, bool]]] = {}
    if not solver_dir.is_dir():
        return {}
    for fname in sorted(os.listdir(solver_dir)):
        fpath = solver_dir / fname
        if not fpath.is_file():
            continue
        if fname.lower().endswith((".dll", ".lib", ".xml")):
            continue
        is_this_jar = fname.lower().endswith(".jar")
        base = fname[:-4] if fname.lower().endswith(".exe") else fname
        if is_this_jar:
            base = base[:-4]
        for display, (prefix, is_jar) in SOLVER_FAMILIES.items():
            if wanted and display not in wanted:
                continue
            if is_this_jar != is_jar:
                continue
            if not base.startswith(prefix):
                continue
            version = base[len(prefix):]
            found.setdefault(display, []).append((_version_key(base), version, fpath, is_jar))
    return {
        name: [(version, path, is_jar) for _key, version, path, is_jar in sorted(entries)]
        for name, entries in found.items()
    }


def solver_command(name: str, path: Path, is_jar: bool, smt2_file: Path) -> list[str]:
    if is_jar:
        cmd = ["java", "-jar", str(path)]
    else:
        cmd = [str(path)]
    cmd += SOLVER_EXTRA_ARGS.get(name, [])
    cmd.append(str(smt2_file))
    return cmd


def group_family_columns(family: str, instances: list[tuple[str, Path, bool]],
                          rows: list["Row"], results: dict) -> list[dict]:
    """Merge consecutive-by-version instances of one family whose results
    are identical across every row into a single report column, so e.g.
    nine z3 versions that all behave the same collapse to one column instead
    of nine. Only *adjacent* versions are merged (a later version that
    reverts to old behavior gets its own column, not silently re-merged)."""
    groups: list[dict] = []
    for version, path, is_jar in instances:
        vector = tuple(
            ((res.grade, res.detail) if (res := results.get(((family, version), row.name))) else None)
            for row in rows
        )
        if groups and groups[-1]["vector"] == vector:
            groups[-1]["versions"].append(version)
        else:
            groups.append({"vector": vector, "versions": [version], "path": path, "is_jar": is_jar})
    return groups


def column_label(family: str, versions: list[str]) -> str:
    if len(versions) == 1:
        return f"{family} {versions[0]}"
    if len(versions) == 2:
        return f"{family} {versions[0]}, {versions[1]}"
    # 3+ versions: an en-dash range reads as "every version in between was
    # tested", which isn't true (e.g. there's no 4.9.x here) -- the caller
    # attaches a footnote enumerating the exact versions actually tested.
    return f"{family} {versions[0]}–{versions[-1]}"


# ---------------------------------------------------------------------------
# Logic discovery
# ---------------------------------------------------------------------------


@dataclass
class Row:
    group: str  # one of GROUP_ORDER
    name: str   # the logic name, as passed to (set-logic ...)
    footnote: str = ""
    legacy: bool = False    # prefix the probe with (set-info :smt-lib-version 2.0)
    no_logic: bool = False  # issue no set-logic command at all (the "(default)" row)


# The first row of the report: no (set-logic ...) command at all, establishing
# what a solver does with no logic selected. There is nothing to grade in a
# script that only sets an option, so the probe declares a symbol instead: a
# solver with a usable default logic answers `success`, one that insists on an
# explicit set-logic first answers with an error.
DEFAULT_ROW_NAME = "(default)"
DEFAULT_ROW_NOTE = (
    "No `set-logic` command is issued at all. Since a script that only sets "
    "an option would report `success` from that option alone, this row's "
    "probe declares a Boolean constant instead -- so it reports whether the "
    "solver has a usable default logic, rather than requiring an explicit "
    "`set-logic` before anything else."
)


# A negative control: ZZZ isn't a real SMT-LIB logic name, so the *correct*
# response is a rejection. Colors are inverted for this one row relative to
# every other row in the table -- see ILLEGAL_LOGIC_NOTE, attached to it
# below -- since here "the solver said success" is the bad outcome.
ILLEGAL_LOGIC_NAME = "ZZZ"
ILLEGAL_LOGIC_NOTE = (
    "Not a real SMT-LIB logic name -- a negative control confirming "
    "set-logic actually validates its argument rather than accepting "
    "anything. Colors are inverted here versus every other row: green "
    "\"rejected\" is the *correct*, expected outcome; red \"allowed\" means "
    "the solver wrongly said `success` to a made-up logic (compare the z3 "
    "4.3.1 footnote above, which does exactly this for every row)."
)


def _logic_name(path: Path) -> str | None:
    """The name after `(logic`, from the file's first line -- None if this
    is a `(theory ...)` file (not a valid set-logic argument)."""
    try:
        with open(path, "r", errors="replace") as f:
            first = f.readline().strip()
    except OSError:
        return None
    m = re.match(r"\(logic\s+(\S+)", first)
    return m.group(1) if m else None


def discover_logics(logics_dir: Path) -> list[Row]:
    current: dict[str, Path] = {}
    have_all = False
    for p in sorted(logics_dir.glob("*.smt2")):
        name = _logic_name(p)
        if p.stem == "ALL":
            have_all = have_all or bool(name)
            continue
        if name:
            current[name] = p

    legacy: dict[str, Path] = {}
    v2_dir = logics_dir / "V2.0"
    for p in sorted(v2_dir.glob("*.smt2")):
        name = _logic_name(p)
        if name and name not in current:
            legacy[name] = p

    # Baseline first -- no logic at all, then ALL -- then the official logics,
    # then the unofficial (2.0-era) ones, each block separated by a heavy rule
    # in the LaTeX rendering.
    rows = [Row("Baseline", DEFAULT_ROW_NAME, DEFAULT_ROW_NOTE, no_logic=True)]
    if have_all:
        rows.append(Row("Baseline", "ALL"))
    rows += [Row("Official", name) for name in sorted(current)]
    rows += [Row("Unofficial", name, legacy=True) for name in sorted(legacy)]
    rows += [Row("Control", ILLEGAL_LOGIC_NAME, ILLEGAL_LOGIC_NOTE)]
    return rows


GROUP_ORDER = ["Baseline", "Official", "Unofficial", "Control"]

# How each group is labelled in the rendered tables. In the LaTeX rendering a
# heavy (double) rule is drawn between consecutive groups; Markdown has no
# equivalent, so there the Group column is what separates the blocks.
GROUP_LABEL = {
    "Baseline": "Baseline",
    "Official": "Official",
    "Unofficial": "Unofficial",
    "Control": "Control",
}

LOGICS_URL = "https://smt-lib.org/logics.shtml"
V2_LOGICS_URL_NOTE = (
    "Not on the current SMT-LIB logics page; carried over from SMT-LIB "
    "2.0's logic set (see SMT/logics/V2.0/ in this repo)."
)
Z3_PRE_4_5_QUIRK = (
    "z3 versions before 4.5.0 do not validate the :logic argument at all -- "
    "`(set-logic X)` for *any* string X, even a nonsense one, returns "
    "`success` (with just a warning on the diagnostic channel: `WARNING: "
    "unknown logic, ignoring set-logic command`). Starting at 4.5.0, z3 "
    "validates the name against its own internal table and answers "
    "`unsupported` for anything not in it. So every row is ✅ in a "
    "pre-4.5.0 z3 column for this reason alone -- treat ✅ there as "
    "\"accepted some string\", not \"recognized this specific logic\"."
)
# The printed table has room for a note, but not for that one: a shorter
# statement of the same fact.
Z3_PRE_4_5_QUIRK_TEX = (
    "z3 before 4.5.0 does not validate the set-logic argument at all: any "
    "string, even a nonsense one, returns success (with only a warning on the "
    "diagnostic channel). Every row is therefore marked in this column for "
    "that reason alone -- read it as \"accepted some string\", not "
    "\"recognized this logic\". From 4.5.0 z3 validates the name and answers "
    "unsupported for anything it does not know."
)

# ---------------------------------------------------------------------------
# Running probes
# ---------------------------------------------------------------------------


# A binary that times out on this many consecutive rows is treated as unusable on
# this platform and not probed further. The verdicts would all be the same, and at
# a realistic timeout the wasted wall time is enough to exceed the CI job limit.
ABANDON_AFTER = 3
ABANDONED_DETAIL = ("not probed: the solver timed out on the first "
                    f"{ABANDON_AFTER} rows, so the binary appears unusable on this platform")


@dataclass
class Result:
    grade: str  # "Y", "P", "N"
    detail: str = ""


def truncate(text: str, limit: int) -> str:
    if len(text) <= limit:
        return text
    cut = text[:limit]
    space = cut.rfind(" ")
    if space > limit * 0.6:
        cut = cut[:space]
    return cut + "..."


def run_row(family: str, path: Path, is_jar: bool, row: Row, timeout: float, workdir: Path) -> Result:
    if row.no_logic:
        # See DEFAULT_ROW_NOTE: no set-logic, and a declaration rather than a
        # bare option so there is something meaningful to grade.
        script = "(set-option :print-success true)\n(declare-fun jsmtlib_probe () Bool)\n"
    else:
        preamble = "(set-info :smt-lib-version 2.0)\n" if row.legacy else ""
        script = f"{preamble}(set-option :print-success true)\n(set-logic {row.name})\n"

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", dir=workdir, delete=False
    ) as f:
        f.write(script)
        tmpname = f.name
    try:
        cmd = solver_command(family, path, is_jar, Path(tmpname))
        # Popen rather than subprocess.run(timeout=...): run() only attaches the
        # partial output to TimeoutExpired on Windows -- on POSIX it kills the
        # process and re-raises with nothing -- so a timeout there would report no
        # detail at all. Collecting it explicitly after the kill works everywhere,
        # and the difference matters: "timed out having already printed success" and
        # "timed out having printed nothing" are completely different diagnoses.
        #
        # stdin is closed deliberately. The script is passed as a file argument, so
        # nothing should be read from stdin; a solver that reads it anyway would
        # block forever rather than fail visibly.
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    stdin=subprocess.DEVNULL, text=True, cwd=workdir)
        except OSError as e:
            return Result("N", f"exec failed: {e}")

        try:
            out, err = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            proc.kill()
            try:
                # Bounded: kill() reaches the solver, but any grandchild it spawned
                # survives holding the pipe open, and an unbounded communicate() then
                # blocks forever -- trading a timed-out probe for a hung report.
                out, err = proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                out, err = "", ""
            def _first(stream: str) -> str:
                lines = [ln.strip() for ln in (stream or "").splitlines() if ln.strip()]
                return " / ".join(lines[:3])
            o, e2 = _first(out), _first(err)
            if o or e2:
                where = "; ".join(x for x in (f"stdout: {o}" if o else "",
                                              f"stderr: {e2}" if e2 else "") if x)
                return Result("P", truncate(f"timeout after {timeout}s ({where})", 200))
            return Result("P", f"timeout after {timeout}s, no output")

        stdout_lines = [ln.strip() for ln in out.splitlines() if ln.strip()]
        stderr_lines = [ln.strip() for ln in err.splitlines() if ln.strip()]

        if not stdout_lines:
            reason = "no output"
            err_line = next((ln for ln in stderr_lines if "error" in ln.lower()), "")
            if err_line:
                reason = err_line
            elif proc.returncode != 0:
                reason = f"exit code {proc.returncode}"
            return Result("N", truncate(reason, 200))

        # Grade the response to set-logic specifically, which is the *second*
        # response: (set-option :print-success true) is acknowledged first, and
        # set-logic answers next. (For a legacy row the leading set-info precedes
        # print-success and so is silent; for the "(default)" row the second
        # command is the declare-fun. Both still land at index 1.)
        #
        # Taking the last line instead -- as this did originally -- misreads any
        # solver that emits something *after* its verdict. z3 4.3.1/4.3.2 on ARM64
        # answer both commands correctly and then fail to stop at end of input,
        # emitting a spurious `(error "line 3 ...: unexpected character")` and
        # hanging; the real verdict was already on line 2. A solver that does not
        # acknowledge set-option produces only one line, and then last and second
        # are the same thing, so this is never worse than the old rule.
        verdict = stdout_lines[1] if len(stdout_lines) >= 2 else stdout_lines[-1]
        if verdict.lower() == "unsupported":
            return Result("N", "unsupported")
        # Match the actual SMT-LIB error response shape, `(error "...")`, not
        # a bare "error" substring.
        if re.match(r"^\(\s*error\b", verdict, re.IGNORECASE):
            return Result("N", truncate(verdict, 200))
        if verdict == "success":
            return Result("Y")
        return Result("P", truncate(verdict, 200))
    finally:
        try:
            os.unlink(tmpname)
        except OSError:
            pass


# ---------------------------------------------------------------------------
# Markdown rendering
# ---------------------------------------------------------------------------

GRADE_SYMBOL = {"Y": "✅", "P": "⚠️", "N": "❌"}


def visual_width(s: str) -> int:
    """Best-effort *display* width, not len(). ✅/❌ are Unicode
    East-Asian-Width "Wide" and render as two monospace columns in any
    editor/terminal, though Python's len() counts them as one; the warning
    sign renders wide too once paired with the variation-selector that makes
    it "emoji style" (its own formal width is "Narrow", but that's not how
    it actually displays here), and that selector itself draws no column of
    its own. Not a general Unicode-width implementation -- just enough to
    keep this report's fixed, known set of table-cell symbols aligned."""
    width = 0
    for ch in s:
        if ch == "\uFE0F":  # variation selector-16: zero-width modifier
            continue
        if ch in ("✅", "❌", "⚠") or unicodedata.east_asian_width(ch) in ("W", "F"):
            width += 2
        else:
            width += 1
    return width


def render_table(header: list[str], rows: list[list[str]]) -> list[str]:
    """Render a GitHub-markdown table with cells padded to a common column
    width, so it's readable as plain text (not just when rendered)."""
    all_rows = [header] + rows
    widths = [max(visual_width(r[i]) for r in all_rows) for i in range(len(header))]

    def fmt_row(r: list[str]) -> str:
        return "| " + " | ".join(cell + " " * (widths[i] - visual_width(cell)) for i, cell in enumerate(r)) + " |"

    lines = [fmt_row(header), "|" + "|".join("-" * (w + 2) for w in widths) + "|"]
    lines += [fmt_row(r) for r in rows]
    return lines


def render_markdown(
    columns: list[dict],
    results: dict[tuple[tuple[str, str], str], Result],
    rows: list[Row],
) -> str:
    lines = []
    lines.append("# SMT solver logic-name support report (`set-logic`)")
    lines.append("")
    lines.append(
        "Generated by `SMTTests/reports/logics-report.py`. For every named "
        "logic jSMTLIB knows about (other than `ALL`, covered separately by "
        "`ALL-logic-report.py`), this checks only whether `(set-logic L)` "
        "gets a plain `success` response -- not whether the solver can "
        f"actually do anything useful in that logic. See <{LOGICS_URL}> for "
        "the current, authoritative SMT-LIB logic list."
    )
    lines.append("")
    lines.append(
        "The first two rows are a baseline: `(default)` issues no `set-logic` "
        "at all, and `ALL` selects the catch-all logic. \"Official\" rows are "
        "every logic under `SMT/logics/` in this repo (the current, "
        "SMT-LIB-2.7-era set). \"Unofficial\" rows are logic names found only "
        "under `SMT/logics/V2.0/` -- names that existed in the SMT-LIB 2.0 "
        "logic set but have since been renamed, folded into a newer logic, or "
        "dropped; included here since some solvers (or scripts written against "
        "older solvers) may still use them. The final \"Control\" row is a "
        "deliberately invalid name."
    )
    lines.append("")
    lines.append(
        "Every version of z3/yices2 found alongside the current release is "
        "tested too, not just the newest. Consecutive versions of a family "
        "that answer every single row identically are merged into one "
        "column: two versions are listed directly (e.g. `yices2 2.6.5, "
        "2.7.0`), three or more are shown as a `first–last` range with a "
        "footnote spelling out exactly which versions that covers; a "
        "version that behaves differently -- even on just one row -- gets "
        "its own column."
    )
    lines.append("")
    lines += render_table(
        ["✅ success", "⚠️ timeout / ambiguous response", "❌ unsupported, error, or no response"],
        [],
    )
    lines.append("")

    footnotes: list[str] = []
    footnote_index: dict[str, int] = {}

    def footnote_marker(text: str) -> str:
        if text not in footnote_index:
            footnotes.append(text)
            footnote_index[text] = len(footnotes)
        return f"[^{footnote_index[text]}]"

    header = ["Group", "Logic"]
    for c in columns:
        label = column_label(c["family"], c["versions"])
        # z3 versions before 4.5.0 don't validate the logic name at all --
        # (set-logic X) for literally any string X returns `success` (with
        # only a warning on the diagnostic channel), so every row in such a
        # column is trivially Y. Flag the column itself rather than every
        # individual cell.
        if c["family"] == "z3" and _version_key(c["versions"][0]) < [4, 5, 0]:
            label += footnote_marker(Z3_PRE_4_5_QUIRK)
        # column_label's en-dash range (3+ versions) only names the first and
        # last; spell out exactly which versions were tested so the range
        # doesn't read as "every version in between was tested too".
        if len(c["versions"]) > 2:
            note = f"Versions tested: {', '.join(c['versions'])}."
            label += footnote_marker(note)
        header.append(label)

    # Inverted relative to GRADE_SYMBOL: for the "Illegal" row, a solver
    # correctly *rejecting* the made-up logic is the good, green outcome.
    ILLEGAL_SYMBOL = {"Y": "❌ allowed", "N": "✅ rejected", "P": "⚠️ ambiguous"}

    table_rows: list[list[str]] = []
    for group in GROUP_ORDER:
        group_label = GROUP_LABEL[group]
        if group == "Unofficial":
            group_label += footnote_marker(V2_LOGICS_URL_NOTE)
        for row in [r for r in rows if r.group == group]:
            logic_label = row.name
            if row.footnote:
                logic_label += footnote_marker(row.footnote)
            cells = [group_label, logic_label]
            for c in columns:
                label = column_label(c["family"], c["versions"])
                rep_version = c["versions"][0]
                res = results.get(((c["family"], rep_version), row.name))
                if res is None:
                    cells.append("—")
                    continue
                symbol = ILLEGAL_SYMBOL[res.grade] if group == "Control" else GRADE_SYMBOL[res.grade]
                if res.detail:
                    note_text = f"**{label} / {row.name}**: {res.detail}"
                    symbol += footnote_marker(note_text)
                cells.append(symbol)
            table_rows.append(cells)
    lines += render_table(header, table_rows)

    if footnotes:
        lines.append("")
        lines.append("---")
        lines.append("")
        lines.append("### Footnotes")
        lines.append("")
        for i, text in enumerate(footnotes, 1):
            lines.append(f"[^{i}]: {text}")

    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# LaTeX rendering
# ---------------------------------------------------------------------------

# A bullet for "accepted", an open circle for the ambiguous/timeout case, and
# an empty cell for "rejected" -- print wants a quiet table, and an empty cell
# reads as "no" without adding ink. $\bullet$/$\circ$ need no extra packages.
LATEX_GRADE = {"Y": r"$\bullet$", "P": r"$\circ$", "N": ""}

LATEX_SPECIAL = {
    "\\": r"\textbackslash{}", "&": r"\&", "%": r"\%", "$": r"\$", "#": r"\#",
    "_": r"\_", "{": r"\{", "}": r"\}", "~": r"\textasciitilde{}",
    "^": r"\textasciicircum{}",
}


# Note text is written for the Markdown report, so it contains things that are
# meaningless or actively broken in print: the grade emoji, typographic dashes
# and quotes (which the tutorial's inputenc/fontenc setup renders as mojibake).
LATEX_TEXT_SUBS = {
    "✅": "an accepted cell", "❌": "a rejected cell", "⚠️": "an ambiguous cell",
    "⚠": "an ambiguous cell", "️": "",
    "–": "--", "—": "---", "“": "``", "”": "''", "‘": "`", "’": "'",
}


def latex_escape(s: str) -> str:
    """Escape LaTeX specials, and turn the notes' Markdown-isms (backtick code
    spans, emoji, typographic punctuation) into something sane in print."""
    for k, v in LATEX_TEXT_SUBS.items():
        s = s.replace(k, v)
    s = s.replace("`", "'")
    out = []
    for ch in s:
        if ord(ch) > 127:          # anything else non-ASCII would be mojibake
            continue
        out.append(LATEX_SPECIAL.get(ch, ch))
    return "".join(out)


def render_latex(
    columns: list[dict],
    results: dict[tuple[tuple[str, str], str], Result],
    rows: list[Row],
) -> str:
    """An upright table. It is deliberately *not* a sidewaystable: merging
    same-behaviour solver versions collapses the columns to about seven, so the
    table comes out tall and narrow (roughly 200pt wide against a 390pt text
    width), and rotating it would push the ~45 rows off the page edge.
    \\scriptsize keeps table, caption and notes together on one page.

    threeparttable is deliberately not used either: it constrains the caption
    and notes to the *table's* width, which here is about half the text width,
    leaving them in an unreadable ribbon. The notes are set full width instead.

    Per-cell detail notes from the Markdown report are dropped -- there are far
    too many to print -- but column-level notes (the pre-4.5.0 z3 quirk, and
    which versions a merged column covers) are kept, since without them a
    merged column heading is misleading.
    """
    notes: list[tuple[str, str]] = []
    seen: dict[str, str] = {}

    def note_mark(text: str) -> str:
        if text not in seen:
            seen[text] = chr(ord("a") + len(seen))
            notes.append((seen[text], text))
        return "$^{\\rm %s}$" % seen[text]

    header = ["{\\bf Group}", "{\\bf Logic}"]
    for c in columns:
        label = latex_escape(column_label(c["family"], c["versions"]))
        if c["family"] == "z3" and _version_key(c["versions"][0]) < [4, 5, 0]:
            label += note_mark(Z3_PRE_4_5_QUIRK_TEX)
        if len(c["versions"]) > 2:
            label += note_mark("Versions tested: %s." % ", ".join(c["versions"]))
        # A short column heading would collide with its neighbours at this
        # width, so each is set in a narrow ragged-right box.
        header.append("\\begin{tabular}{@{}c@{}}%s\\end{tabular}" % _wrap_heading(label))

    body: list[str] = []
    body.append("\\hline")
    body.append(" & ".join(header) + " \\\\")
    for group in GROUP_ORDER:
        grows = [r for r in rows if r.group == group]
        if not grows:
            continue
        # A heavy (double) rule separates the blocks: (default)+ALL, the
        # official logics, the unofficial ones, then the control row.
        body.append("\\hline\\hline")
        first = True
        for row in grows:
            cells = [GROUP_LABEL[group] if first else "",
                     "{\\tt %s}" % latex_escape(row.name)]
            first = False
            for c in columns:
                res = results.get(((c["family"], c["versions"][0]), row.name))
                cells.append("--" if res is None else LATEX_GRADE[res.grade])
            body.append(" & ".join(cells) + " \\\\")

    n = len(columns)
    out = []
    out.append("%% Generated by SMTTests/reports/logics-report.py --tex -- do not edit by hand.")
    out.append("")
    out.append("\\begin{table}[p]")
    out.append("\\centering")
    out.append("\\scriptsize")
    out.append("\\renewcommand{\\arraystretch}{0.9}")
    out.append("\\begin{tabular}{|l|l|" + "c|" * n + "}")
    out += body
    out.append("\\hline")
    out.append("\\end{tabular}")
    # The blocks and caveats are explained in the appendix text, so the caption
    # is just the legend -- a long caption plus the notes would not fit here.
    out.append("\\caption{Logic names accepted by each solver. $\\bullet$ marks a {\\tt success} "
               "response, $\\circ$ an ambiguous response or a timeout, and an empty cell an "
               "{\\tt unsupported} or error response. For the {\\tt ZZZ} control row an empty "
               "cell is the {\\em correct} outcome.}")
    out.append("\\label{tab:supported-logics}")
    if notes:
        out.append("\\begin{flushleft}\\scriptsize")
        for mark, text in notes:
            out.append("$^{\\rm %s}$ %s\\par" % (mark, latex_escape(text)))
        out.append("\\end{flushleft}")
    out.append("\\end{table}")
    out.append("")
    return "\n".join(out)


def _wrap_heading(label: str) -> str:
    """Break a column heading such as "z3 4.5.0--5.1.0" onto its own lines, so
    the narrow numeric columns are not forced wide by their headings."""
    return "\\\\".join(label.split(" ", 1)) if " " in label else label



# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> int:
    # Windows consoles default to a legacy code page (cp1252 on the CI runners),
    # which cannot encode the report's grade symbols. Writing files is handled by
    # explicit encoding= arguments; this covers --out - and the progress output.
    for _stream in (sys.stdout, sys.stderr):
        try:
            _stream.reconfigure(encoding="utf-8")
        except (AttributeError, OSError):
            pass

    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver-dir", type=Path, default=None, help="Directory containing solver binaries (default: auto-detected Solvers-<platform> next to this checkout)")
    ap.add_argument("--solvers", type=str, default=None, help="Comma-separated subset of solver names to test (default: all discovered)")
    ap.add_argument("--logics-dir", type=Path, default=None, help="Directory containing logic .smt2 definitions with a V2.0/ subdirectory (default: ../../SMT/logics next to this checkout)")
    ap.add_argument("--timeout", type=float, default=10.0, help="Per-row timeout in seconds (default: 10)")
    ap.add_argument("--out", type=Path, default=Path("Logics.md"), help="Markdown output file (default: Logics.md; pass - for stdout)")
    ap.add_argument("--tex", type=Path, default=None, help="Also write a LaTeX table to this file (for the tutorial's 'SMT-LIB Logics supported by solvers' appendix). Written from the same probe run as --out, so the two cannot disagree.")
    ap.add_argument("--json", type=Path, default=None, help="Also write raw, per-solver-version results as JSON. Unlike the tables, nothing is merged or collapsed, so results from several platforms can be compared version-by-version (see combine-logics-reports.py).")
    ap.add_argument("--platform-label", type=str, default=None, help="Name recorded as the platform in --json output (default: auto-detected from the solver directory).")
    args = ap.parse_args()

    solver_dir = args.solver_dir or default_solver_dir()
    wanted = set(args.solvers.split(",")) if args.solvers else None
    instances_by_family = discover_solver_instances(solver_dir, wanted)

    if not instances_by_family:
        print(f"No solvers found in {solver_dir}", file=sys.stderr)
        return 1

    logics_dir = args.logics_dir or default_logics_dir()
    rows = discover_logics(logics_dir)
    if not rows:
        print(f"No logic definitions found in {logics_dir}", file=sys.stderr)
        return 1

    family_order = [n for n in SOLVER_FAMILIES if n in instances_by_family]
    all_instances = [
        (family, version, path, is_jar)
        for family in family_order
        for version, path, is_jar in instances_by_family[family]
    ]
    print(f"Solver directory: {solver_dir}", file=sys.stderr)
    print(f"Logics directory: {logics_dir}", file=sys.stderr)
    print(f"Testing: {', '.join(f'{f} {v}' for f, v, _p, _j in all_instances)}", file=sys.stderr)
    print(f"Logics: {len(rows)}", file=sys.stderr)

    results: dict[tuple[tuple[str, str], str], Result] = {}
    with tempfile.TemporaryDirectory(prefix="smt-logics-") as workdir:
        workdir_path = Path(workdir)
        total = len(all_instances) * len(rows)
        done = 0
        for family, version, path, is_jar in all_instances:
            consecutive_timeouts = 0
            abandoned = False
            for row in rows:
                if abandoned:
                    results[((family, version), row.name)] = Result("P", ABANDONED_DETAIL)
                    done += 1
                    continue
                res = run_row(family, path, is_jar, row, args.timeout, workdir_path)
                results[((family, version), row.name)] = res
                if res.grade == "P" and res.detail.startswith("timeout"):
                    consecutive_timeouts += 1
                else:
                    consecutive_timeouts = 0
                if consecutive_timeouts >= ABANDON_AFTER:
                    # Nothing is learned by timing out another 40-odd times, and the
                    # cost is real: on linux-arm64 the two z3 4.3.x binaries hang on
                    # every row, and at a 30s timeout that alone is 45 minutes --
                    # enough to blow the CI job limit (run 36739244137 was cancelled
                    # for exactly this). Record the rest as not probed, and let the
                    # combined report say "unusable here" once instead of 45 times.
                    abandoned = True
                    print(f"  abandoning {family} {version}: timed out on "
                          f"{ABANDON_AFTER} consecutive rows", file=sys.stderr)
                done += 1
                if done % 25 == 0 or done == total:
                    print(f"  {done}/{total}", file=sys.stderr)

    columns = [
        {"family": family, "versions": g["versions"]}
        for family in family_order
        for g in group_family_columns(family, instances_by_family[family], rows, results)
    ]

    md = render_markdown(columns, results, rows)
    if str(args.out) == "-":
        print(md)
    else:
        args.out.write_text(md, encoding="utf-8")
        print(f"Wrote {args.out}", file=sys.stderr)

    if args.tex:
        args.tex.write_text(render_latex(columns, results, rows), encoding="utf-8")
        print(f"Wrote {args.tex}", file=sys.stderr)

    if args.json:
        # Deliberately *not* the merged columns the tables use: which versions
        # merge is itself platform-dependent, so a cross-platform comparison has
        # to be made version by version.
        payload = {
            "platform": args.platform_label or solver_dir.name,
            "solver_dir": str(solver_dir),
            "logics_dir": str(logics_dir),
            "rows": [{"group": r.group, "name": r.name} for r in rows],
            "solvers": [f"{f} {v}" for f, v, _p, _j in all_instances],
            "results": {
                f"{family} {version}": {
                    row.name: {"grade": res.grade, "detail": res.detail}
                    for row in rows
                    if (res := results.get(((family, version), row.name))) is not None
                }
                for family, version, _p, _j in all_instances
            },
        }
        args.json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        print(f"Wrote {args.json}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
