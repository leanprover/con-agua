#!/usr/bin/env python3
"""One-shot scaffold: derive ConAgua/Arena/Inst1.lean and Inst1Spec.lean from Lift.lean and
LiftSpec.lean (lane `exprops`, 2026-10-21).

`instantiate1Go` has `liftLooseBVarsGo`'s shape (cut-off, five memoized arms rebuilding through
`mk_*`); this script renames (lift -> inst, c -> d, k -> v, lfSch -> imSch, ...), inserts the arms'
view checks after the memo probe (the twin probes before viewing), and writes the dispatcher and
the program by hand-written templates. The two output files are ordinary Lean, maintained by hand
afterwards; running this script on the committed Lift files reproduces them as committed.

Usage (from the repository root): python3 scripts/inst1_from_lift.py [--check]
"""
import re, sys

A = 'ConAgua/Arena/'

def subst_cd(t):
    t = re.sub(r'\bc\b', 'd', t)
    return re.sub(r'\bk\b', 'v', t)

def inst1(src):
    out = HEADER
    i = src.index("/-- **The model of `lift_app`.** -/")
    j = src.index("end\n\n/-! ### Continuations and guarded equations -/")
    arms = src[i:j]
    for a, b in [("lift_app", "inst_app"), ("lift_lam", "inst_lam"), ("lift_forall", "inst_forall"),
                 ("lift_let", "inst_let"), ("lift_proj", "inst_proj"), ("liftAppW", "instAppW"),
                 ("liftLamW", "instLamW"), ("liftForallW", "instForallW"), ("liftLetW", "instLetW"),
                 ("liftProjW", "instProjW"), ("liftW n", "instW n"), ("lfSch", "imSch"),
                 ("LMEMO", "IMEMO"), ("lsetK h c", "isetK h c")]:
        arms = arms.replace(a, b)
    for nm, c0 in [("instAppW", 4), ("instLamW", 28), ("instForallW", 30), ("instLetW", 20),
                   ("instProjW", 32)]:
        k = arms.index(f"def {nm}")
        k2 = arms.index("    else\n      match instW n m", k)
        arms = (arms[:k2] + "    else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none\n"
                f"    else if rdW (m.arr64 CTL) ({c0} + tierW h) ≤ idxW h then none\n" + arms[k2:])
    out += subst_cd(arms) + "end\n"
    i = src.index("/-- The arms after each child (first-order continuations")
    j = src.index("section arms\nvariable (n : Nat) (m : Mem) (h c k : Word)")
    ks = src[i:j]
    for a, b in [("appK₁", "iappK₁"), ("appK₂", "iappK₂"), ("lamK₁", "ilamK₁"), ("lamK₂", "ilamK₂"),
                 ("faK₁", "ifaK₁"), ("faK₂", "ifaK₂"), ("leK₁", "ileK₁"), ("leK₂", "ileK₂"),
                 ("leK₃", "ileK₃"), ("pjK₁", "ipjK₁"), ("lsetK", "isetK"), ("liftW", "instW"),
                 ("lfSch", "imSch")]:
        ks = ks.replace(a, b)
    ks = ks.replace("appK₁_some'", "iappK₁_some").replace("appK₂_some'", "iappK₂_some")
    ks = subst_cd(ks).replace("section ks", "section iks").replace("end ks", "end iks")
    out += "\n/-! ### Continuations and guarded equations -/\n\n" + ks
    i = src.index("/-- An arm's memo hit (the same for every arm")
    j = src.index("end arms")
    eq = src[i:j]
    for a, b in [("liftAppW", "instAppW"), ("liftLamW", "instLamW"), ("liftForallW", "instForallW"),
                 ("liftLetW", "instLetW"), ("liftProjW", "instProjW"), ("liftW", "instW"),
                 ("lfSch", "imSch"), ("LMEMO", "IMEMO"), ("appK₁", "iappK₁"), ("lamK₁", "ilamK₁"),
                 ("faK₁", "ifaK₁"), ("leK₁", "ileK₁"), ("pjK₁", "ipjK₁")]:
        eq = eq.replace(a, b)
    eq = subst_cd(eq)
    for nm, c0 in [("instAppW", 4), ("instLamW", 28), ("instForallW", 30), ("instLetW", 20),
                   ("instProjW", 32)]:
        tn = nm.replace("W", "W_miss")
        k = eq.index(f"theorem {tn}")
        k2 = eq.index(":\n", k)
        eq = eq[:k2] + f" (hvk : viewOK m h {c0})" + eq[k2:]
    eq = eq.replace("ne_eq, not_true_eq_false]\n",
                    "ne_eq, not_true_eq_false, hvk.1, ↓reduceIte, UInt64.not_le.mpr hvk.2]\n")
    out += "\n" + DISPATCH_EQS + eq + "end arms\n\n"
    gp = ['instW_cut', 'instW_app', 'instW_lam', 'instW_forall', 'instW_let', 'instW_proj',
          'instW_bvar_eq', 'instW_bvar_gt', 'instW_bvar_lt', 'instW_leaf']
    out += ''.join(f"grind_pattern [arena_grind] {g} => instW (n + 1) m h d v\n" for g in gp)
    for nm in ['instAppW', 'instLamW', 'instForallW', 'instLetW', 'instProjW']:
        out += f"grind_pattern [arena_grind] {nm}_hit => {nm} (n + 1) m h d v\n"
        out += f"grind_pattern [arena_grind] {nm}_miss => {nm} (n + 1) m h d v\n"
    out = out.replace("  (hvk : viewOK", "\n    (hvk : viewOK")
    out = re.sub(r"\(hvk : viewOK m h (\d+)\):", r"(hvk : viewOK m h \1) :", out)
    i = src.index("def liftApp : FunDecl")
    j = src.index("/-! ## The program and its specs -/")
    code = src[i:j]
    for a, b in [("liftApp", "instApp"), ("liftLam", "instLam"), ("liftForall", "instForall"),
                 ("liftLet", "instLet"), ("liftProj", "instProj"), ("lift_go", "inst_go"),
                 ("lf_find", "if_find"), ("lf_put", "if_put"), ("LMEMO", "IMEMO")]:
        code = code.replace(a, b)
    code = code.replace("(fd, j, d)", "(fd, j, e0)").replace("locals (fd, j, d,", "locals (fd, j, e0,")
    code = subst_cd(code)
    for nm, c0 in [("instApp", 4), ("instLam", 28), ("instForall", 30), ("instLet", 20),
                   ("instProj", 32)]:
        k = code.index(f"def {nm} : FunDecl")
        k2 = code.index("  i := h & 134217727;\n", k) + len("  i := h & 134217727;\n")
        code = (code[:k2] + "  if t != 0 && CTL.u64[1] == 0 { abort };\n"
                f"  if CTL.u64[{c0} + t] <= i {{ abort }};\n" + code[k2:])
    return out + "\n" + GO + code + PROG

def inst1spec(s):
    s = s.replace("public import ConAgua.Arena.Lift\n",
                  "public import ConAgua.Arena.Inst1\npublic import ConAgua.Arena.LiftSpec\n")
    i = s.index("/-!\n# The specs"); j = s.index("-/\n", i) + 3
    s = s[:i] + SPEC_DOC + s[j:]
    for a, b in SPEC_RENAMES:
        s = s.replace(a, b)
    i = s.index("section specs"); j = s.index("end specs")
    s = s[:i] + subst_cd(s[i:j]) + s[j:]
    s = s.replace("    finish (gen := 20) [tierW, idxW]", "    finish (gen := 20) [viewOK, tierW, idxW]")
    i = s.index("/-! ## `lift_entry(h, k, c)`")
    return s[:i] + SPEC_ENTRY

exec(open('scripts/inst1_templates.py').read())

if __name__ == '__main__':
    o1 = inst1(open(A + 'Lift.lean').read())
    o2 = inst1spec(open(A + 'LiftSpec.lean').read())
    if '--check' in sys.argv:
        ok = o1 == open(A + 'Inst1.lean').read() and o2 == open(A + 'Inst1Spec.lean').read()
        print('identical' if ok else 'DIFFERENT'); sys.exit(0 if ok else 1)
    open(A + 'Inst1.lean', 'w').write(o1); open(A + 'Inst1Spec.lean', 'w').write(o2)
