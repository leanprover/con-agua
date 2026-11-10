"""Vocabulary hook of the re-proof ladder (rung iii): the attribute sets instead of pasted lemma names.

Name it in a sync's rules file as `vocab_hook vocab_attr.py` (scripts/reproof-ladder.py, VOCAB HOOK).
`candidates(proof, ctx)` gets the codemod text of a base proof and returns its variants, tried in
order (the ladder keeps the first that elaborates):

  sets      the encodings' grind sets (`SETS`) added to every `grind [`, `grind only [`, `sym [`,
            `sym only [` and `finish [` list that lacks them, and to a bare `finish`;
  sets+     the same with the costly sets too (`SETS_PLUS`: definitions unfolded, kept out of the
            everyday sets because every importer that names those pays for them);
  specs     `sets+`, and the tagged-load spec set (`SPEC_SCOPES`, scoped `@[spec]` sets) opened
            in front of every tactic line that starts with `vcgen` or `sym` (vcgen reads one
            global `@[spec]` set, so a named set is a scoped one: `open scoped S in vcgen [...]`);
  iwok      `sets`, and a positional destructuring of the pool invariant (`obtain ⟨h1, …⟩ := X.iw`
            / `.ok` / `.iwok`) replaced by `have hIWOK := X.iw`, each destructured name by its field
            (`hIWOK.iw`, `hIWOK.er`, …: the k-th name is the k-th field of `IWOK_FIELDS`, so a base
            proof written when `IWOK` had fewer fields still names the right ones, as long as new
            fields are appended), and the anonymous-constructor proof of an `IWOK` that follows it
            (`exact ⟨…⟩`, or `refine ⟨?_, …⟩` and its bullets) by `IWOK_GRIND`;
  rules:N   then the sync's own `[vocab N]` sections of the rules file, in order (text rules the
            sync needed besides the sets).

The sets live in ConAgua/Arena/ErecVocab.lean (`arena_grind`, `erec_grind`, `L.Arena.ErecSpec`) and
ConAgua/Arena/IWFrame.lean (`ind_grind`); a sync that moves another encoding adds its set here.
"""
import re

SETS = ["arena_grind"]
SETS_PLUS = ["erec_grind"]
SPEC_SCOPES = ["L.Arena.ErecSpec"]
IWOK_GRIND = "grind [IWOK_iff, ind_grind, iwTop, erTop, erecTop1]"
# `L.Ind.IWOK`'s fields in declaration order (ConAgua/Arena/IndIface.lean)
IWOK_FIELDS = ["iw", "er", "iwSize", "erSize", "ctl", "er1", "er1Size", "erCap", "er1Cap"]

# a list opener: `grind [`, `grind only [`, `sym only [`, `finish [`, `finish (gen := 20) [`
LIST = re.compile(r"\b(grind|sym|finish)\b((?:\s+only)?(?:\s*\([^()]*\))*)\s*\[")
BARE_FINISH = re.compile(r"\bfinish\b((?:\s*\([^()]*\))*)(?=\s*(?:$|<;>|\)|;))", re.M)


def _close(text, i):
    """Index of the `]` matching the `[` at text[i]."""
    d = 0
    for j in range(i, len(text)):
        c = text[j]
        if c in "[(⟨{":
            d += 1
        elif c in "])⟩}":
            d -= 1
            if d == 0:
                return j
    return -1


def add_sets(text, sets=SETS):
    out, pos = [], 0
    for m in LIST.finditer(text):
        if m.start() < pos:
            continue
        lb = m.end() - 1
        rb = _close(text, lb)
        if rb < 0:
            continue
        items = text[lb + 1:rb]
        missing = [s for s in sets if not re.search(r"\b%s\b" % re.escape(s), items)]
        out.append(text[pos:rb])
        if missing:
            out.append((", " if items.strip() else "") + ", ".join(missing))
        pos = rb
    out.append(text[pos:])
    text = "".join(out)
    # a bare `finish` (no list): give it one
    return BARE_FINISH.sub(lambda m: f"finish{m.group(1)} [{', '.join(sets)}]", text)


def open_specs(text, scopes=SPEC_SCOPES):
    """`open scoped S in` in front of each tactic line starting with `vcgen` or `sym` (inside a
    `sym … =>` block only the `sym` line: the block is grind mode, where `open … in` does not parse)."""
    pre = "".join(f"open scoped {s} in " for s in scopes)
    lines, sym_ind = text.split("\n"), None
    for k, l in enumerate(lines):
        if not l.strip():
            continue
        ind = len(l) - len(l.lstrip())
        if sym_ind is not None and ind <= sym_ind:
            sym_ind = None
        m = re.match(r"^(\s*(?:· )?)((?:vcgen|sym)\b.*)$", l)
        if m and sym_ind is None:
            lines[k] = m.group(1) + pre + m.group(2)
            if m.group(2).startswith("sym"):
                sym_ind = ind
    return "\n".join(lines)


OBTAIN = re.compile(r"(?m)^(\s*)obtain ⟨([\w'₀-₉]+(?:,\s*[\w'₀-₉]+)*)⟩ := (\S+\.(?:iw|ok|iwok))\s*$")


def _block_end(lines, i, ind):
    """First line after line i whose indentation is <= ind (the end of i's tactic)."""
    j = i + 1
    while j < len(lines) and (not lines[j].strip() or len(lines[j]) - len(lines[j].lstrip()) > ind):
        j += 1
    return j


def iwok(text):
    lines = text.split("\n")
    i, changed = 0, False
    while i < len(lines):
        m = OBTAIN.match(lines[i])
        if not m:
            i += 1
            continue
        ind = len(m.group(1))
        names = [n.strip() for n in m.group(2).split(",")]
        lines[i] = f"{m.group(1)}have hIWOK := {m.group(3)}"
        changed = True
        # the rest of this tactic block (same indentation)
        j = i + 1
        while j < len(lines):
            l = lines[j]
            if l.strip() and len(l) - len(l.lstrip()) < ind:
                break
            s = l.strip()
            lind = len(l) - len(l.lstrip())
            if lind == ind and (s.startswith("exact ⟨") or re.match(r"refine ⟨(\?_,\s*)*\?_⟩$", s)):
                e = _block_end(lines, j, ind)
                # bullets of a refine at the same indentation
                if s.startswith("refine"):
                    while e < len(lines) and lines[e].strip().startswith("·") and \
                            len(lines[e]) - len(lines[e].lstrip()) == ind:
                        e = _block_end(lines, e, ind)
                lines[j:e] = [" " * ind + IWOK_GRIND]
            else:
                for k, n in enumerate(names[:len(IWOK_FIELDS)]):
                    if n != "_":
                        lines[j] = re.sub(r"(?<![\w.'])%s(?![\w'₀-₉])" % re.escape(n),
                                          f"hIWOK.{IWOK_FIELDS[k]}", lines[j])
            j += 1
        i += 1
    return "\n".join(lines) if changed else None


def candidates(proof, ctx):
    out = []
    s = add_sets(proof)
    out.append(("sets", s))
    s2 = add_sets(s, SETS + SETS_PLUS)
    out.append(("sets+", s2))
    out.append(("specs", open_specs(s2)))
    w = iwok(s)
    if w is not None:
        out.append(("iwok", w))
    rules = ctx.get("rules")
    for lab, rs in (getattr(rules, "vocab", None) or {}).items():
        out.append((f"rules:{lab}", type(rules).apply(rs, proof, ctx.get("text", ""))))
    return out
