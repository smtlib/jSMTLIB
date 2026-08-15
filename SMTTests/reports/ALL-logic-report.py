#!/usr/bin/env python3
"""Probe each configured SMT solver's support for the capabilities that make
up jSMTLIB's ALL logic and emit a GitHub-flavored markdown table.

(set-logic ALL) is required of every SMT-LIB-compliant solver, but what it
actually *supports* within that logic is solver-defined. This script probes
that directly: for each solver, it runs small, self-contained SMT-LIB scripts
-- one per capability row -- and checks whether the solver's response matches
a known-correct answer computed by construction (mostly ground facts, so "is
this satisfiable" is decidable by inspection, not by trusting the solver).

The capability list is derived from jSMTLIB's own logic/theory definitions
under SMT/logics/: ALL.smt2 declares :theories (Core ArraysEx Reals_Ints
FloatingPoint FixedSizeBitVectors Strings HO-Core), and each probe group
below corresponds to one of those seven theories (Reals_Ints is split into
Ints / Reals / Arithmetic variants for readability), plus a Quantifiers group
(a core language feature, not tied to one theory) and a Datatypes group
(declare-datatype/declare-datatypes are *not* one of ALL's seven theories --
see the Datatypes footnote -- but are close to universally expected).

Closely related functions (e.g. bvand/bvor, or all five BitVector overflow
predicates) are tested together in a single row/probe rather than one row
each, to keep the table a reasonable size; see REFERENCES below (and in the
generated report) for links to the authoritative SMT-LIB 2.7 theory pages
instead of restating their definitions here.

Grading per probe:
  Y (yes)     - solver's check-sat answer matches the expected sat/unsat.
  ~ (partial) - solver accepted the script (no error) but returned `unknown`,
                or timed out.
  N (no)      - solver rejected the script (error/crash) or returned the
                *wrong* sat/unsat verdict (a soundness bug, not just a
                missing feature -- the detail footnote says which).

Usage:
  python3 ALL-logic-report.py [--solver-dir DIR] [--solvers NAME[,NAME...]]
                               [--groups GROUP[,GROUP...]] [--timeout SECONDS]
                               [--out FILE]

With no arguments, discovers the platform-appropriate Solvers-* directory
next to this checkout (../../OpenJML21/Solvers/Solvers-<platform>), tests
every version present of each of z3, cvc5, yices2, bitwuzla, alt-ergo,
smtinterpol (not just the newest -- consecutive versions of a family that
behave identically across every probe are merged into one report column),
runs every probe, and writes ALL-logic-report.md.
"""

from __future__ import annotations

import argparse
import os
import platform
import re
import struct
import subprocess
import sys
import tempfile
import unicodedata
from dataclasses import dataclass
from pathlib import Path

# ---------------------------------------------------------------------------
# Solver discovery
# ---------------------------------------------------------------------------

# display name -> (filename prefix, is_jar)
SOLVER_FAMILIES = {
    "z3": ("z3-", False),
    "cvc5": ("cvc5-", False),
    "yices2": ("yices2-", False),
    "bitwuzla": ("bitwuzla-", False),
    "alt-ergo": ("alt-ergo-", False),
    "smtinterpol": ("smtinterpol-", True),
}

# Extra CLI arguments some solvers need/benefit from for clean batch output.
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


def _version_key(name: str):
    return [int(n) for n in re.findall(r"\d+", name)]


def discover_solver_instances(solver_dir: Path, wanted=None) -> dict[str, list[tuple[str, Path, bool]]]:
    """Every matching binary for each solver family in solver_dir -- not just
    the newest -- as {family: [(version, path, is_jar), ...]} sorted oldest
    to newest. Version is read straight from the filename (e.g. z3-4.16.0 ->
    4.16.0) rather than parsed from each solver's own --version banner, whose
    format varies wildly across solvers."""
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
                          probes: list["Probe"], results: dict) -> list[dict]:
    """Merge consecutive-by-version instances of one family whose results
    are identical across every probe into a single report column, so e.g.
    nine z3 versions that all behave the same collapse to one column instead
    of nine. Only *adjacent* versions are merged (a later version that
    reverts to old behavior gets its own column, not silently re-merged)."""
    groups: list[dict] = []
    for version, path, is_jar in instances:
        vector = tuple(
            ((res.grade, res.detail) if (res := results.get(((family, version), probe.name))) else None)
            for probe in probes
        )
        if groups and groups[-1]["vector"] == vector:
            groups[-1]["versions"].append(version)
        else:
            groups.append({"vector": vector, "versions": [version], "path": path, "is_jar": is_jar})
    return groups


def column_label(family: str, versions: list[str]) -> str:
    if len(versions) == 1:
        return f"{family} {versions[0]}"
    return f"{family} {versions[0]}–{versions[-1]}"


# ---------------------------------------------------------------------------
# Probe definitions
# ---------------------------------------------------------------------------


@dataclass
class Probe:
    group: str
    name: str
    body: str  # SMT-LIB commands after set-logic/set-option, before check-sat/exit
    expect: str  # "sat" or "unsat"
    footnote: str = ""


PROBES: list[Probe] = []


def add(group: str, name: str, body: str, expect: str, footnote: str = "") -> None:
    PROBES.append(Probe(group, name, body.strip() + "\n", expect, footnote))


def fp_r(value: float) -> str:
    """`((_ to_fp 8 24) RNE <value>)` -- the safe way to construct an exact
    FP32 constant from a Real literal, used throughout the FloatingPoint
    probes instead of hand-derived bit patterns."""
    return f"((_ to_fp 8 24) RNE {value})"


def fp32_bits_hex(value: float) -> str:
    """Exact IEEE-754 binary32 bit pattern for `value`, as an SMT-LIB hex
    literal, computed via Python's own struct module rather than hand-derived
    to eliminate transcription risk."""
    (as_int,) = struct.unpack(">I", struct.pack(">f", value))
    return f"#x{as_int:08x}"


# References to the authoritative SMT-LIB 2.7 definitions, shown once per
# group in the generated report instead of restating theory content inline.
GROUP_LINKS = {
    "Core": "https://smt-lib.org/theories-Core.shtml",
    "Quantifiers": "https://smt-lib.org/papers/smt-lib-reference-v2.7-r2026-03-27.pdf",
    "Ints": "https://smt-lib.org/theories-Reals_Ints.shtml",
    "Reals": "https://smt-lib.org/theories-Reals_Ints.shtml",
    "Arithmetic variants": "https://smt-lib.org/theories-Reals_Ints.shtml",
    "Arrays": "https://smt-lib.org/theories-ArraysEx.shtml",
    "BitVectors": "https://smt-lib.org/theories-FixedSizeBitVectors.shtml",
    "Strings": "https://smt-lib.org/theories-UnicodeStrings.shtml",
    "FloatingPoint": "https://smt-lib.org/theories-FloatingPoint.shtml",
    "HO-Core": "https://smt-lib.org/theories-HO-Core.shtml",
    "Datatypes": "https://smt-lib.org/papers/smt-lib-reference-v2.7-r2026-03-27.pdf",
}

# ---- Core -------------------------------------------------------------
add(
    "Core",
    "Bool sort & connectives (not/and/or/xor/=>/=/distinct/ite)",
    """
(assert (and true (not false) (or false true) (=> false true) (xor true false)
             (= 1 1) (not (distinct 2 2)) (= (ite true 1 2) 1)))
""",
    "sat",
)

# ---- Quantifiers ----------------------------------------------------------
add(
    "Quantifiers",
    "exists",
    """
(declare-fun p (Int) Bool)
(assert (p 3))
(assert (exists ((x Int)) (p x)))
""",
    "sat",
    "Mainly validates syntax acceptance: a solver that (incorrectly) treats "
    "`exists` as vacuously true would still answer `sat` here.",
)
add(
    "Quantifiers",
    "forall (instantiation forces a contradiction)",
    """
(declare-fun p (Int) Bool)
(assert (forall ((x Int)) (p x)))
(assert (not (p 5)))
""",
    "unsat",
)
add(
    "Quantifiers",
    "nested/alternating forall-exists",
    """
(declare-fun p (Int Int) Bool)
(assert (forall ((x Int)) (exists ((y Int)) (p x y))))
(assert (forall ((x Int) (y Int)) (not (p x y))))
""",
    "unsat",
)
add(
    "Quantifiers",
    "forall with :pattern annotation",
    """
(declare-fun f (Int) Int)
(assert (forall ((x Int)) (! (= (f x) x) :pattern ((f x)))))
(assert (not (= (f 5) 5)))
""",
    "unsat",
)
add(
    "Quantifiers",
    "quantifier over Array sort",
    """
(declare-fun a () (Array Int Int))
(assert (forall ((i Int)) (= (select a i) 5)))
(assert (not (= (select a 3) 5)))
""",
    "unsat",
)

# ---- Ints (part of Reals_Ints) --------------------------------------------
add(
    "Ints",
    "+, - (n-ary, unary & binary)",
    "(assert (and (= (+ 2 3 4) 9) (= (- (- 5)) 5) (= (- 10 3 2) 5)))",
    "sat",
)
add(
    "Ints",
    "*, div, mod, abs",
    """
(assert (and (= (* 2 3 4) 24)
             (= (div 7 2) 3) (= (div (- 7) 2) (- 4))
             (= (mod 7 2) 1) (= (mod (- 7) 2) 1)
             (= (abs (- 5)) 5)))
""",
    "sat",
    "div/mod use Euclidean semantics (remainder always in [0,|n|), not "
    "truncating/floor division); the negative-dividend case catches a "
    "truncating-division implementation.",
)
add("Ints", "<=/</>=/> (chainable)", "(assert (< 1 2 3))", "sat")
add(
    "Ints",
    "(_ divisible n) indexed predicate",
    '(assert ((_ divisible 3) 9))',
    "sat",
)

# ---- Reals (part of Reals_Ints) -------------------------------------------
add(
    "Reals",
    "+, - (n-ary, unary & binary)",
    "(assert (and (= (+ 1.5 2.25) 3.75) (= (- (- 1.5)) 1.5) (= (- 5.0 1.5) 3.5)))",
    "sat",
)
add(
    "Reals",
    "*, /",
    "(assert (and (= (* 2.0 3.5) 7.0) (= (/ 7.0 2.0) 3.5)))",
    "sat",
)
add("Reals", "<=/</>=/> (chainable)", "(assert (< 1.0 2.5 3.0))", "sat")
add(
    "Reals",
    "to_real, to_int, is_int",
    """
(assert (and (= (to_real 5) 5.0)
             (= (to_int 3.7) 3) (= (to_int (- 1.3)) (- 2))
             (is_int 4.0) (not (is_int 4.5))))
""",
    "sat",
    "to_int rounds toward -infinity (floor), not truncation -- e.g. "
    "`(to_int (- 1.3))` is `-2`, not `-1`.",
)

# ---- Linear vs nonlinear arithmetic (explicit differentiator) -------------
add(
    "Arithmetic variants",
    "LIA (linear Int: constant * variable)",
    "(declare-fun x () Int)\n(assert (= (* 3 x) 12))",
    "sat",
)
add(
    "Arithmetic variants",
    "NIA (nonlinear Int: variable * variable)",
    "(declare-fun x () Int)\n(assert (= (* x x) 16))\n(assert (> x 0))",
    "sat",
    "x^2=16 can't be discharged by substitution/linearization.",
)
add(
    "Arithmetic variants",
    "LRA (linear Real: constant * variable)",
    "(declare-fun x () Real)\n(assert (= (* 2.5 x) 10.0))",
    "sat",
)
add(
    "Arithmetic variants",
    "NRA (nonlinear Real: variable * variable)",
    "(declare-fun x () Real)\n(assert (= (* x x) 6.25))\n(assert (> x 0.0))",
    "sat",
)
add(
    "Arithmetic variants",
    "Exponentiation (^)",
    "(declare-fun x () Real)\n(assert (= (^ x 2) 9.0))\n(assert (> x 0.0))",
    "sat",
    "`^` is not an SMT-LIB operator in any theory; some solvers (e.g. z3) "
    "support it as a non-standard extension.",
)

# ---- Arrays (ArraysEx) -----------------------------------------------------
add(
    "Arrays",
    "select/store (write-then-read; disjoint index unaffected)",
    """
(declare-fun a () (Array Int Int))
(assert (= (select (store a 0 42) 0) 42))
(assert (= (select a 1) 7))
(assert (not (= (select (store a 0 42) 1) 7)))
""",
    "unsat",
)
add(
    "Arrays",
    "nested arrays (Array of Array)",
    """
(declare-fun a () (Array Int (Array Int Int)))
(assert (= (select (select a 0) 0) 5))
""",
    "sat",
)
add(
    "Arrays",
    "extensionality",
    """
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (forall ((i Int)) (= (select a i) (select b i))))
(assert (not (= a b)))
""",
    "unsat",
    "Combines quantifiers with the extensionality axiom; `unknown` here can "
    "happen even with full select/store support, since it needs quantifier "
    "instantiation over an array sort.",
)

# ---- BitVectors (FixedSizeBitVectors), 8-bit throughout -------------------
add("BitVectors", "sort & literals (#b/#x)", "(assert (= #b00001111 #x0f))", "sat")
add(
    "BitVectors",
    "concat / extract",
    """
(assert (and (= (concat #b0000 #b1111) #b00001111)
             (= ((_ extract 3 0) #b11110101) #b0101)))
""",
    "sat",
)
add(
    "BitVectors",
    "bvnot / bvneg",
    """
(assert (and (= (bvnot #b00001111) #b11110000)
             (= (bvneg #b00000001) #b11111111)))
""",
    "sat",
)
add(
    "BitVectors",
    "bvand / bvor",
    """
(assert (and (= (bvand #b11001100 #b10101010) #b10001000)
             (= (bvor #b11001100 #b10101010) #b11101110)))
""",
    "sat",
)
add(
    "BitVectors",
    "bvadd / bvmul",
    """
(assert (and (= (bvadd #b00000001 #b00000001) #b00000010)
             (= (bvmul #b00000011 #b00000100) #b00001100)))
""",
    "sat",
)
add(
    "BitVectors",
    "bvudiv / bvurem",
    """
(assert (and (= (bvudiv #b00001100 #b00000100) #b00000011)
             (= (bvurem #b00001101 #b00000100) #b00000001)))
""",
    "sat",
)
add(
    "BitVectors",
    "bvshl / bvlshr",
    """
(assert (and (= (bvshl #b00000001 #b00000010) #b00000100)
             (= (bvlshr #b00001000 #b00000010) #b00000010)))
""",
    "sat",
)
add("BitVectors", "bvult", "(assert (bvult #b00000011 #b00000100))", "sat")
add(
    "BitVectors",
    "overflow predicates (bvnego/bvuaddo/bvsaddo/bvumulo/bvsmulo)",
    """
(assert (and (bvnego #b10000000)
             (bvuaddo #b11111111 #b00000001)
             (bvsaddo #b01111111 #b00000001)
             (bvumulo #b11111111 #b00000010)
             (bvsmulo #b01000000 #b00000010)))
""",
    "sat",
    "2023 addition to FixedSizeBitVectors.",
)
add(
    "BitVectors",
    "ubv_to_int / sbv_to_int / int_to_bv",
    """
(assert (= (ubv_to_int #b11111111) 255))
(assert (= (sbv_to_int #b11111111) (- 1)))
(assert (= ((_ int_to_bv 8) 255) #b11111111))
""",
    "sat",
    "Renamed/finalized as recently as 2024-07/2025-02, so expect this to be "
    "the least-supported BitVector row.",
)

# ---- Strings ----------------------------------------------------------------
add(
    "Strings",
    "str.++ / str.len",
    '(assert (and (= (str.++ "ab" "cd") "abcd") (= (str.len "hello") 5)))',
    "sat",
)
add(
    "Strings",
    "str.< / str.<= (lexicographic)",
    '(assert (and (str.< "abc" "abd" "abe") (str.<= "abc" "abc")))',
    "sat",
)
add(
    "Strings",
    "str.at / str.substr",
    '(assert (and (= (str.at "hello" 1) "e") (= (str.substr "hello world" 6 5) "world")))',
    "sat",
)
add(
    "Strings",
    "str.prefixof / str.suffixof / str.contains / str.indexof",
    """
(assert (and (str.prefixof "he" "hello") (str.suffixof "lo" "hello")
             (str.contains "hello" "ell") (= (str.indexof "hello" "l" 0) 2)))
""",
    "sat",
)
add(
    "Strings",
    "str.replace / str.replace_all",
    '(assert (and (= (str.replace "hello" "l" "L") "heLlo") (= (str.replace_all "hello" "l" "L") "heLLo")))',
    "sat",
)
add(
    "Strings",
    "str.is_digit, str.to_code/from_code, str.to_int/from_int",
    """
(assert (and (str.is_digit "5") (not (str.is_digit "a"))
             (= (str.to_code "A") 65) (= (str.from_code 65) "A")
             (= (str.to_int "123") 123) (= (str.from_int 123) "123")))
""",
    "sat",
)
add(
    "Strings",
    "str.to_re / str.in_re, RE constants (re.none/re.all/re.allchar)",
    """
(assert (and (str.in_re "abc" (str.to_re "abc"))
             (not (str.in_re "x" re.none))
             (str.in_re "anything" re.all)
             (str.in_re "x" re.allchar) (not (str.in_re "xy" re.allchar))))
""",
    "sat",
)
add(
    "Strings",
    "RE set ops (re.++/re.union/re.inter)",
    """
(assert (and (str.in_re "ab" (re.++ (str.to_re "a") (str.to_re "b")))
             (str.in_re "a" (re.union (str.to_re "a") (str.to_re "b")))
             (str.in_re "a" (re.inter (str.to_re "a") re.all))))
""",
    "sat",
)
add(
    "Strings",
    "re.* / re.+ / re.opt (closure operators)",
    """
(assert (and (str.in_re "aaa" (re.* (str.to_re "a")))
             (not (str.in_re "" (re.+ (str.to_re "a"))))
             (str.in_re "" (re.opt (str.to_re "a")))))
""",
    "sat",
)
add(
    "Strings",
    "re.comp / re.diff",
    '(assert (and (str.in_re "b" (re.comp (str.to_re "a"))) (str.in_re "b" (re.diff re.allchar (str.to_re "a")))))',
    "sat",
)
add(
    "Strings",
    "re.range / re.^ / re.loop (indexed/parametric)",
    """
(assert (and (str.in_re "c" (re.range "a" "z"))
             (str.in_re "aaa" ((_ re.^ 3) (str.to_re "a")))
             (str.in_re "aa" ((_ re.loop 1 3) (str.to_re "a")))))
""",
    "sat",
)
add(
    "Strings",
    "str.replace_re / str.replace_re_all",
    """
(assert (and (= (str.replace_re "xaay" (str.to_re "a") "Z") "xZay")
             (= (str.replace_re_all "xaay" (str.to_re "a") "Z") "xZZy")))
""",
    "sat",
)

# ---- FloatingPoint ------------------------------------------------------
add(
    "FloatingPoint",
    "sort, literals, Float16/32/64/128 aliases, rounding modes",
    """
(declare-fun x () (_ FloatingPoint 8 24))
(assert (= x (_ +zero 8 24)))
(assert (not (= (_ +oo 8 24) (_ -oo 8 24))))
(assert (= (_ NaN 8 24) (_ NaN 8 24)))
(declare-fun y () Float32)
(assert (= y (_ +zero 8 24)))
(assert (and (= RNE roundNearestTiesToEven) (= RNA roundNearestTiesToAway)
             (= RTP roundTowardPositive) (= RTN roundTowardNegative)
             (= RTZ roundTowardZero) (not (= RNE RTZ))))
""",
    "sat",
    "The `_ NaN = _ NaN` conjunct uses `=` (structural equality, reflexive) "
    "not `fp.eq` (IEEE equality, false for NaN) -- see the fp.eq row.",
)
add(
    "FloatingPoint",
    "to_fp from Real / fp.to_real",
    f"(assert (and (= (fp.to_real {fp_r(3.0)}) 3.0) (= (fp.to_real (_ +zero 8 24)) 0.0)))",
    "sat",
)
add(
    "FloatingPoint",
    "fp.add / fp.sub / fp.mul / fp.div",
    f"""
(assert (and (= (fp.add RNE {fp_r(1.0)} {fp_r(2.0)}) {fp_r(3.0)})
             (= (fp.sub RNE {fp_r(5.0)} {fp_r(2.0)}) {fp_r(3.0)})
             (= (fp.mul RNE {fp_r(2.0)} {fp_r(3.0)}) {fp_r(6.0)})
             (= (fp.div RNE {fp_r(6.0)} {fp_r(2.0)}) {fp_r(3.0)})))
""",
    "sat",
    "Operands are small exact powers/products of two, so there's no "
    "rounding-mode ambiguity.",
)
add(
    "FloatingPoint",
    "fp.fma / fp.sqrt / fp.rem / fp.roundToIntegral",
    f"""
(assert (and (= (fp.fma RNE {fp_r(2.0)} {fp_r(3.0)} {fp_r(1.0)}) {fp_r(7.0)})
             (= (fp.sqrt RNE {fp_r(4.0)}) {fp_r(2.0)})
             (= (fp.rem {fp_r(7.0)} {fp_r(3.0)}) {fp_r(1.0)})
             (= (fp.roundToIntegral RNE {fp_r(3.0)}) {fp_r(3.0)})))
""",
    "sat",
    "fp.rem: 7 rem 3 = 7 - 3*round(7/3) = 7 - 3*2 = 1 (no tie-break "
    "ambiguity, unlike e.g. 7 rem 2).",
)
add(
    "FloatingPoint",
    "fp.min/max, fp.leq/lt/geq/gt (ordering, chainable)",
    f"""
(assert (and (= (fp.min {fp_r(2.0)} {fp_r(5.0)}) {fp_r(2.0)})
             (= (fp.max {fp_r(2.0)} {fp_r(5.0)}) {fp_r(5.0)})
             (fp.lt {fp_r(1.0)} {fp_r(2.0)} {fp_r(3.0)})))
""",
    "sat",
)
add(
    "FloatingPoint",
    "fp.eq (IEEE equality: +0=-0, NaN != NaN)",
    "(assert (and (fp.eq (_ +zero 8 24) (_ -zero 8 24)) (not (fp.eq (_ NaN 8 24) (_ NaN 8 24)))))",
    "sat",
    "Deliberately the opposite of the vocabulary row's structural-`=` "
    "conjunct: fp.eq treats +0/-0 as equal and NaN/NaN as unequal.",
)
add(
    "FloatingPoint",
    "fp.abs / fp.neg",
    "(assert (and (= (fp.abs (_ -oo 8 24)) (_ +oo 8 24)) (= (fp.neg (_ +oo 8 24)) (_ -oo 8 24))))",
    "sat",
)
add(
    "FloatingPoint",
    "classification predicates (isNormal/isSubnormal/isZero/isInfinite/isNaN/isNegative/isPositive)",
    f"""
(assert (fp.isZero (_ +zero 8 24)))
(assert (fp.isInfinite (_ +oo 8 24)))
(assert (fp.isNaN (_ NaN 8 24)))
(assert (fp.isNegative (_ -zero 8 24)))
(assert (fp.isPositive (_ +zero 8 24)))
(assert (fp.isNormal {fp_r(1.0)}))
(assert (not (fp.isSubnormal {fp_r(1.0)})))
""",
    "sat",
)
add(
    "FloatingPoint",
    "Conversions: to_fp (bitvector-IEEE / FP / signed-bv / unsigned-bv), fp.to_ubv/to_sbv",
    f"""
(assert (= ((_ to_fp 8 24) {fp32_bits_hex(1.0)}) {fp_r(1.0)}))
(assert (= (fp.to_real ((_ to_fp 11 53) RNE {fp_r(3.0)})) 3.0))
(assert (= ((_ to_fp 8 24) RNE #b00000101) {fp_r(5.0)}))
(assert (= ((_ to_fp_unsigned 8 24) RNE #b11111111) {fp_r(255.0)}))
(assert (= ((_ fp.to_ubv 8) RNE {fp_r(5.0)}) #b00000101))
(assert (= ((_ fp.to_sbv 8) RNE {fp_r(-5.0)}) #b11111011))
""",
    "sat",
    "The bitvector-IEEE-format literal is the exact binary32 encoding of "
    "1.0, computed via Python's `struct` module.",
)

# ---- HO-Core ----------------------------------------------------------------
add(
    "HO-Core",
    "function sort (->), @ application, lambda",
    """
(declare-fun f () (-> Int Int))
(assert (and (= (@ f 5) 5) (= (@ (lambda ((x Int)) (+ x 1)) 5) 6)))
""",
    "sat",
)

# ---- Datatypes (not one of ALL's seven theories -- see footnote) ---------
add(
    "Datatypes",
    "declare-datatype (enum & recursive, with selector)",
    """
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-fun c () Color)
(assert (= c Red))
(declare-datatype IList ((nil) (cons (head Int) (tail IList))))
(declare-fun l () IList)
(assert (= l (cons 1 nil)))
(assert (= (head l) 1))
""",
    "sat",
    "declare-datatype/declare-datatypes are not among ALL's seven listed "
    "theories (SMT/logics/ALL.smt2) but are near-universally expected.",
)
add(
    "Datatypes",
    "declare-datatypes (mutually recursive, plural form)",
    """
(declare-datatypes ((Tree 0) (Forest 0))
  (((leaf) (node (val Int) (children Forest)))
   ((empty) (add (hd Tree) (tl Forest)))))
(declare-fun t () Tree)
(assert (= t leaf))
""",
    "sat",
)
add(
    "Datatypes",
    "tester ((_ is C) x)",
    """
(declare-datatype Color ((Red) (Green) (Blue)))
(declare-fun c () Color)
(assert ((_ is Red) c))
""",
    "sat",
)
add(
    "Datatypes",
    "match expression",
    """
(declare-datatype IList ((nil) (cons (head Int) (tail IList))))
(declare-fun l () IList)
(assert (= l (cons 5 nil)))
(assert (= (match l ((nil 0) ((cons h t) h))) 5))
""",
    "sat",
)


GROUP_ORDER = [
    "Core",
    "Quantifiers",
    "Ints",
    "Reals",
    "Arithmetic variants",
    "Arrays",
    "BitVectors",
    "Strings",
    "FloatingPoint",
    "HO-Core",
    "Datatypes",
]

# ---------------------------------------------------------------------------
# Running probes
# ---------------------------------------------------------------------------


@dataclass
class Result:
    grade: str  # "Y", "P", "N"
    detail: str = ""


VERDICT_RE = re.compile(r"^(sat|unsat|unknown)$")


def truncate(text: str, limit: int) -> str:
    """Truncate at a word boundary rather than mid-word."""
    if len(text) <= limit:
        return text
    cut = text[:limit]
    space = cut.rfind(" ")
    if space > limit * 0.6:  # don't chop off most of the string looking for a space
        cut = cut[:space]
    return cut + "..."


def run_probe(name: str, path: Path, is_jar: bool, probe: Probe, timeout: float, workdir: Path) -> Result:
    script = f"(set-logic ALL)\n(set-option :print-success false)\n{probe.body}(check-sat)\n(exit)\n"
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".smt2", dir=workdir, delete=False
    ) as f:
        f.write(script)
        tmpname = f.name
    try:
        cmd = solver_command(name, path, is_jar, Path(tmpname))
        try:
            proc = subprocess.run(
                cmd, capture_output=True, text=True, timeout=timeout
            )
        except subprocess.TimeoutExpired:
            return Result("P", "timeout")
        except OSError as e:
            return Result("N", f"exec failed: {e}")

        stdout_lines = [ln.strip() for ln in proc.stdout.splitlines()]
        stderr_lines = [ln.strip() for ln in proc.stderr.splitlines()]

        verdict = None
        for ln in reversed(stdout_lines):
            if VERDICT_RE.match(ln):
                verdict = ln
                break

        if verdict is None:
            reason = "no sat/unsat/unknown in output"
            err_line = next(
                (ln for ln in stdout_lines + stderr_lines if "error" in ln.lower()),
                "",
            )
            if err_line:
                reason = err_line
            elif proc.returncode != 0:
                reason = f"exit code {proc.returncode}"
            return Result("N", truncate(reason, 200))

        if verdict == "unknown":
            return Result("P", "unknown")
        if verdict == probe.expect:
            return Result("Y")
        return Result("N", f"WRONG ANSWER: expected {probe.expect}, got {verdict}")
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
    probes: list[Probe],
) -> str:
    lines = []
    lines.append("# SMT solver capability report (`(set-logic ALL)`)")
    lines.append("")
    lines.append(
        "Generated by `SMTTests/reports/ALL-logic-report.py`. Every SMT-LIB-compliant "
        "solver must accept `(set-logic ALL)`, but what it actually supports "
        "within that logic is solver-defined; each row is one small, "
        "self-contained probe script with a known-correct answer (mostly "
        "ground facts), run directly against each solver binary. Closely "
        "related functions are tested together in one row rather than one "
        "row each -- see the References table below for the authoritative "
        "definition of each group instead of restating it here."
    )
    lines.append("")
    lines.append(
        "Every version of z3/yices2 found alongside the current release is "
        "tested too, not just the newest. Consecutive versions of a family "
        "that answer every single probe identically are merged into one "
        "column, labeled with the version range they cover (e.g. `z3 "
        "4.3.1–4.8.12`); a version that behaves differently -- even on "
        "just one probe -- gets its own column."
    )
    lines.append("")
    lines += render_table(
        ["✅ supported and correct", "⚠️ accepted but `unknown`/timeout", "❌ rejected, crashed, or wrong answer"],
        [],
    )
    lines.append("")

    lines.append("### References")
    lines.append("")
    ref_rows = [
        [group, f"<{GROUP_LINKS[group]}>"] for group in GROUP_ORDER if group in GROUP_LINKS
    ]
    lines += render_table(["Group", "SMT-LIB 2.7 definition"], ref_rows)
    lines.append("")

    header = ["Group", "Capability"] + [
        column_label(c["family"], c["versions"]) for c in columns
    ]

    footnotes: list[str] = []
    footnote_index: dict[str, int] = {}

    def footnote_marker(text: str) -> str:
        if text not in footnote_index:
            footnotes.append(text)
            footnote_index[text] = len(footnotes)
        return f"[^{footnote_index[text]}]"

    table_rows: list[list[str]] = []
    for group in GROUP_ORDER:
        for probe in [p for p in probes if p.group == group]:
            cells = [group, probe.name]
            for c in columns:
                label = column_label(c["family"], c["versions"])
                rep_version = c["versions"][0]
                res = results.get(((c["family"], rep_version), probe.name))
                if res is None:
                    cells.append("—")  # em dash: solver not present
                    continue
                symbol = GRADE_SYMBOL[res.grade]
                if res.detail:
                    note_text = f"**{label} / {probe.name}**: {res.detail}"
                    symbol += footnote_marker(note_text)
                cells.append(symbol)
            if probe.footnote:
                marker = footnote_marker(probe.footnote)
                cells[1] += marker
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
    ap.add_argument("--groups", type=str, default=None, help=f"Comma-separated subset of capability groups to run (default: all). Choices: {', '.join(GROUP_ORDER)}")
    ap.add_argument("--timeout", type=float, default=10.0, help="Per-probe timeout in seconds (default: 10)")
    ap.add_argument("--out", type=Path, default=Path("ALL-logic-report.md"), help="Output file (default: ALL-logic-report.md; pass - for stdout)")
    args = ap.parse_args()

    solver_dir = args.solver_dir or default_solver_dir()
    wanted = set(args.solvers.split(",")) if args.solvers else None
    instances_by_family = discover_solver_instances(solver_dir, wanted)

    if not instances_by_family:
        print(f"No solvers found in {solver_dir}", file=sys.stderr)
        return 1

    probes = PROBES
    if args.groups:
        wanted_groups = set(args.groups.split(","))
        unknown = wanted_groups - set(GROUP_ORDER)
        if unknown:
            print(f"Unknown group(s): {', '.join(sorted(unknown))}", file=sys.stderr)
            return 1
        probes = [p for p in PROBES if p.group in wanted_groups]

    family_order = [n for n in SOLVER_FAMILIES if n in instances_by_family]
    all_instances = [
        (family, version, path, is_jar)
        for family in family_order
        for version, path, is_jar in instances_by_family[family]
    ]
    print(f"Solver directory: {solver_dir}", file=sys.stderr)
    print(f"Testing: {', '.join(f'{f} {v}' for f, v, _p, _j in all_instances)}", file=sys.stderr)
    print(f"Probes: {len(probes)}", file=sys.stderr)

    results: dict[tuple[tuple[str, str], str], Result] = {}
    with tempfile.TemporaryDirectory(prefix="smt-capability-") as workdir:
        workdir_path = Path(workdir)
        total = len(all_instances) * len(probes)
        done = 0
        for family, version, path, is_jar in all_instances:
            for probe in probes:
                res = run_probe(family, path, is_jar, probe, args.timeout, workdir_path)
                results[((family, version), probe.name)] = res
                done += 1
                if done % 25 == 0 or done == total:
                    print(f"  {done}/{total}", file=sys.stderr)

    columns = [
        {"family": family, "versions": g["versions"]}
        for family in family_order
        for g in group_family_columns(family, instances_by_family[family], probes, results)
    ]

    md = render_markdown(columns, results, probes)
    if str(args.out) == "-":
        print(md)
    else:
        args.out.write_text(md)
        print(f"Wrote {args.out}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
