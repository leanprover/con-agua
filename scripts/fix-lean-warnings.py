#!/usr/bin/env python3
"""Apply the mechanical fixes Lean's linters suggest, from a `lake build` log.

Adapted from con-ron's scripts/fix-lean-warnings.py.  Usage (from the repository root, the
directory the log's paths are relative to):

    scripts/lake build 2>&1 | tee build.log
    python3 scripts/fix-lean-warnings.py build.log [--only simp|vars|deprecated]

Three warning kinds are fixed:

* `linter.unusedSimpArgs` ("This simp argument is unused: X"): X is dropped
  from its simp call by Mathlib's `fix_unused_simp_args.py` (vendored next to
  this script; `← X` becomes `- X`).  The log
  is deduplicated first, since the same warning can be printed more than
  once, and a list that becomes empty (`simp only []`, `simp []`) is written
  as `simp only` or `simp` and a list left starting with `[ ` loses the
  space, but only on the lines the fix touched.
* `linter.unusedVariables` ("Variable name `x` is not explicitly
  referenced"): `x` becomes `_x`, which is the linter's own `[apply]` hint.
  The identifier must be exactly at the reported line and column (0-based,
  in code points), otherwise the site is reported and skipped.

* `linter.deprecated` ("`X` has been deprecated: Use `Y` instead"): the
  identifier at the reported position is renamed.  It must be spelled there
  as the full old name or as a suffix of it whose prefix the new name shares
  (`div_eq` inside `namespace Nat` → `div_eq_ite`); otherwise the site is
  reported and skipped (a warning raised inside a macro points elsewhere).

Only paths under `ConAgua/` are touched: dependencies, `vendor/` and generated files
are out of scope, and warnings from them are ignored.  Run it once per
build log: a second run over the same log would edit again.
"""
import argparse
import difflib
import importlib.util
import re
import sys
import tempfile
from collections import defaultdict
from pathlib import Path

SIMP_RE = re.compile(r"^warning: (ConAgua/[^:]+\.lean):(\d+):(\d+): This simp argument is unused:\s*$")
VAR_RE = re.compile(r"^warning: (ConAgua/[^:]+\.lean):(\d+):(\d+): Variable name `([^`]+)` is not explicitly referenced\.")
DEP_RE = re.compile(r"^warning: (ConAgua/[^:]+\.lean):(\d+):(\d+): `([^`]+)` has been deprecated: [Uu]se `([^`]+)` instead")
# Columns shifted by the renames of this run: (path, line) -> [(col, delta)].  The log's simp
# positions predate them, so fix_simp moves a position right by the renames before it.
SHIFTS = defaultdict(list)
MATHLIB_FIXER = Path(__file__).resolve().parent / "fix_unused_simp_args.py"


def fix_simp(lines):
    """Run Mathlib's fixer over the deduplicated simp-arg warnings."""
    seen, out = set(), []
    for i, ln in enumerate(lines):
        m = SIMP_RE.match(ln)
        if m and i + 1 < len(lines):
            arg = lines[i + 1].strip()
            path, line, col = m[1], int(m[2]), int(m[3])
            col += sum(d for c, d in SHIFTS[(path, line)] if c < col)
            key = ((path, str(line), str(col)), arg)
            if key not in seen:
                seen.add(key)
                out += [f"warning: {path}:{line}:{col}: This simp argument is unused:", "  " + arg]
    if not seen:
        print("simp: nothing to fix")
        return
    spec = importlib.util.spec_from_file_location("fix_unused_simp_args", MATHLIB_FIXER)
    fixer = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fixer)
    touched = sorted({g[0] for g, _ in seen})
    before = {p: Path(p).read_text() for p in touched if Path(p).exists()}
    with tempfile.NamedTemporaryFile("w", suffix=".log", delete=False) as t:
        t.write("\n".join(out) + "\n")
    orig_remove = fixer.remove_arg

    def remove_arg(text, span, target):
        # Mathlib turns an unused `← X` into `- X` (erasing a simp lemma); a local hypothesis
        # cannot be erased, so drop it.
        bare = target.strip().lstrip("←").strip()
        if target.strip().startswith("←") and re.fullmatch(r"h[\w']*", bare):
            return _drop(text, span, bare)
        return orig_remove(text, span, target)

    def _drop(text, span, bare):
        lb, rb = span
        inner = text[lb + 1 : rb]
        items = fixer.split_top_level(inner)
        for idx, (a, b) in enumerate(items):
            if fixer._bare_name(inner[a:b])[1] != bare or not inner[a:b].strip().startswith("←"):
                continue
            if idx < len(items) - 1:
                ra, rb2 = a, items[idx + 1][0]
            elif idx > 0:
                ra, rb2 = items[idx - 1][1], b
            else:
                ra, rb2 = a, b
            return text[: lb + 1] + inner[:ra] + inner[rb2:] + text[rb:], True
        return text, False

    fixer.remove_arg = remove_arg
    sys.argv = ["fix_unused_simp_args.py", t.name]
    fixer.main()
    tidied = 0
    for p, old_text in before.items():
        old = old_text.splitlines(keepends=True)
        new = Path(p).read_text().splitlines(keepends=True)
        sm = difflib.SequenceMatcher(None, old, new, autojunk=False)
        for tag, _, _, j1, j2 in sm.get_opcodes():
            if tag == "equal":
                continue
            for j in range(j1, j2):
                s = re.sub(r"\bsimp only \[\]", "simp only", new[j])
                s = re.sub(r"\bsimp \[\]", "simp", s)
                s = re.sub(r"\[ +(?=\S)", "[", s)
                if s != new[j]:
                    new[j], tidied = s, tidied + 1
        Path(p).write_text("".join(new))
    print(f"simp: {len(seen)} warnings, {tidied} lines tidied")


def rename_in_decreasing_by(src, line, name):
    """`name` was bound at `line` (1-based) and is now `_name`.  The linter does not see uses
    inside `decreasing_by`, so rename those too (up to the next top-level command)."""
    pat = re.compile(r"(?<![\w.'])" + re.escape(name) + r"(?![\w'!?₀₁₂₃₄₅₆₇₈₉])")
    k, in_dec = line, False
    while k < len(src):
        l = src[k]
        if k >= line and l and not l[0].isspace() and not l.startswith(("termination_by", "decreasing_by", ")", "|")):
            break
        if l.startswith("decreasing_by"):
            in_dec = True
        if in_dec:
            src[k] = pat.sub("_" + name, l)
        k += 1


def reindent_blocks():
    """A rename that lengthens a line moves a `by` block on that line to the right; the block's
    continuation lines (a tactic sequence aligned with its first tactic) must move with it, or
    the block no longer parses.  For each edited line with a `by` after a rename and an
    unclosed bracket, shift the following lines until the bracket closes."""
    opens, closes = "([⟨{", ")]⟩}"
    moved = 0
    by_file = defaultdict(list)
    for (p, line), sh in SHIFTS.items():
        by_file[p].append((line, sh))
    for p, items in by_file.items():
        src = Path(p).read_text().split("\n")
        for line, sh in sorted(items):
            s = src[line - 1]
            for mm in re.finditer(r"(?<![\w.'])by\b", s):
                d = sum(dl for c, dl in sh if c < mm.start())
                if d <= 0:
                    continue
                stack, target = [], None
                for i, ch in enumerate(s):
                    if i == mm.start():
                        target = stack[-1] if stack else None
                    if ch in opens:
                        stack.append(i)
                    elif ch in closes and stack:
                        stack.pop()
                if target is None or target not in stack:
                    continue  # the block is closed on its own line
                depth = stack.index(target)  # brackets still open outside the target's
                k, cur = line, len(stack)
                while cur > depth and k < len(src):
                    t = src[k]
                    src[k] = " " * d + t if t.strip() else t
                    SHIFTS[(p, k + 1)].append((0, d))
                    moved += 1
                    for ch in t:
                        if ch in opens:
                            cur += 1
                        elif ch in closes:
                            cur -= 1
                    k += 1
                break
        Path(p).write_text("\n".join(src))
    print(f"reindent: {moved} continuation lines moved")


def fix_vars(lines):
    edits = defaultdict(set)
    for ln in lines:
        m = VAR_RE.match(ln)
        if m:
            edits[m[1]].add((int(m[2]), int(m[3]), m[4]))
    done = skipped = 0
    for p, es in edits.items():
        src = Path(p).read_text().splitlines(keepends=True)
        for line, col, name in sorted(es, reverse=True):
            orig = col
            col += sum(d for c, d in SHIFTS[(p, line)] if c < col)
            s = src[line - 1]
            end = col + len(name)
            if s[col:end] == name and (end == len(s) or not (s[end].isalnum() or s[end] in "_'!?₀₁₂₃₄₅₆₇₈₉")):
                src[line - 1] = s[:col] + "_" + s[col:]
                SHIFTS[(p, line)].append((orig, 1))
                done += 1
                rename_in_decreasing_by(src, line, name)
            else:
                print(f"  skip {p}:{line}:{col}: `{name}` not at that position")
                skipped += 1
        Path(p).write_text("".join(src))
    print(f"vars: {done} renamed to `_x`, {skipped} skipped")


def fix_deprecated(lines):
    edits = defaultdict(set)
    for ln in lines:
        m = DEP_RE.match(ln)
        if m:
            edits[m[1]].add((int(m[2]), int(m[3]), m[4], m[5]))
    done = skipped = 0
    ident = "_'!?₀₁₂₃₄₅₆₇₈₉."
    for p, es in edits.items():
        src = Path(p).read_text().splitlines(keepends=True)
        retry = set()
        for line, col, old, new in sorted(es, reverse=True):
            s = src[line - 1]
            old_parts, new_parts = old.split("."), new.split(".")
            hit = None
            for k in range(len(old_parts)):  # the full name first, then suffixes
                written = ".".join(old_parts[k:])
                end = col + len(written)
                if s[col:end] != written or (end < len(s) and (s[end].isalnum() or s[end] in ident)):
                    continue
                if old_parts[:k] != new_parts[:k]:
                    continue
                hit = (end, ".".join(new_parts[k:]))
                break
            if hit:
                src[line - 1] = s[:col] + hit[1] + s[hit[0]:]
                SHIFTS[(p, line)].append((col, len(hit[1]) - (hit[0] - col)))
                done += 1
            else:  # raised inside a macro or syntax quotation: fixed file-wide below
                retry.add((old, new))
                skipped += 1
        Path(p).write_text("".join(src))
        if retry:
            text = Path(p).read_text()
            for old, new in sorted(retry):
                pat = re.compile(r"(?<![\w.'])" + re.escape(old) + r"(?![\w.'!?₀₁₂₃₄₅₆₇₈₉])")
                text, n = pat.subn(new, text)
                print(f"  {p}: `{old}` -> `{new}` file-wide ({n} places; the warning is raised by a macro)")
            Path(p).write_text(text)
    print(f"deprecated: {done} renamed, {skipped} sites handled file-wide")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("log")
    ap.add_argument("--only", choices=["simp", "vars", "deprecated"])
    a = ap.parse_args()
    lines = Path(a.log).read_text().splitlines()
    # Renaming keeps line numbers; dropping simp arguments can join lines,
    # so the renames go first, while the log's positions are still exact.
    if a.only in (None, "deprecated"):
        fix_deprecated(lines)
    if a.only in (None, "vars"):
        fix_vars(lines)
    reindent_blocks()
    if a.only in (None, "simp"):
        fix_simp(lines)


if __name__ == "__main__":
    main()
