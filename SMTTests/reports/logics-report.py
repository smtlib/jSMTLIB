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
    group: str  # "Current", "V2.0", or "Illegal"
    name: str   # the logic name, as passed to (set-logic ...)
    footnote: str = ""


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
    for p in sorted(logics_dir.glob("*.smt2")):
        if p.stem == "ALL":
            continue
        name = _logic_name(p)
        if name:
            current[name] = p

    legacy: dict[str, Path] = {}
    v2_dir = logics_dir / "V2.0"
    for p in sorted(v2_dir.glob("*.smt2")):
        name = _logic_name(p)
        if name and name not in current:
            legacy[name] = p

    rows = [Row("Current", name) for name in sorted(current)]
    rows += [Row("V2.0", name) for name in sorted(legacy)]
    rows += [Row("Illegal", ILLEGAL_LOGIC_NAME, ILLEGAL_LOGIC_NOTE)]
    return rows


GROUP_ORDER = ["Current", "V2.0", "Illegal"]

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

# ---------------------------------------------------------------------------
# Running probes
# ---------------------------------------------------------------------------


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
    preamble = "(set-info :smt-lib-version 2.0)\n" if row.group == "V2.0" else ""
    script = f"{preamble}(set-option :print-success true)\n(set-logic {row.name})\n"

    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", dir=workdir, delete=False
    ) as f:
        f.write(script)
        tmpname = f.name
    try:
        cmd = solver_command(family, path, is_jar, Path(tmpname))
        try:
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, cwd=workdir)
        except subprocess.TimeoutExpired:
            return Result("P", "timeout")
        except OSError as e:
            return Result("N", f"exec failed: {e}")

        stdout_lines = [ln.strip() for ln in proc.stdout.splitlines() if ln.strip()]
        stderr_lines = [ln.strip() for ln in proc.stderr.splitlines() if ln.strip()]

        if not stdout_lines:
            reason = "no output"
            err_line = next((ln for ln in stderr_lines if "error" in ln.lower()), "")
            if err_line:
                reason = err_line
            elif proc.returncode != 0:
                reason = f"exit code {proc.returncode}"
            return Result("N", truncate(reason, 200))

        last = stdout_lines[-1]
        if last.lower() == "unsupported":
            return Result("N", "unsupported")
        # Match the actual SMT-LIB error response shape, `(error "...")`, not
        # a bare "error" substring.
        if re.match(r"^\(\s*error\b", last, re.IGNORECASE):
            return Result("N", truncate(last, 200))
        if last == "success":
            return Result("Y")
        return Result("P", truncate(last, 200))
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
        "\"Current\" rows are every logic under `SMT/logics/` in this repo "
        "(the current, SMT-LIB-2.7-era set). \"V2.0 (legacy)\" rows are "
        "logic names found only under `SMT/logics/V2.0/` -- names that "
        "existed in the SMT-LIB 2.0 logic set but have since been renamed, "
        "folded into a newer logic, or dropped; included here since some "
        "solvers (or scripts written against older solvers) may still use "
        "them."
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
        group_label = group
        if group == "V2.0":
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
                symbol = ILLEGAL_SYMBOL[res.grade] if group == "Illegal" else GRADE_SYMBOL[res.grade]
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
# Main
# ---------------------------------------------------------------------------


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--solver-dir", type=Path, default=None, help="Directory containing solver binaries (default: auto-detected Solvers-<platform> next to this checkout)")
    ap.add_argument("--solvers", type=str, default=None, help="Comma-separated subset of solver names to test (default: all discovered)")
    ap.add_argument("--logics-dir", type=Path, default=None, help="Directory containing logic .smt2 definitions with a V2.0/ subdirectory (default: ../../SMT/logics next to this checkout)")
    ap.add_argument("--timeout", type=float, default=10.0, help="Per-row timeout in seconds (default: 10)")
    ap.add_argument("--out", type=Path, default=Path("Logics.md"), help="Output file (default: Logics.md; pass - for stdout)")
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
            for row in rows:
                res = run_row(family, path, is_jar, row, args.timeout, workdir_path)
                results[((family, version), row.name)] = res
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
        args.out.write_text(md)
        print(f"Wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
