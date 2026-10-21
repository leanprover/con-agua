import sys
ND = int(sys.argv[2]); mode = sys.argv[1]   # mode: flat | nested | base
real = ["lit","app","sort","const","letE","bvar","fvar","lam","forallE","proj","zero","succ","max","imax","param","ls","nanon","nstr","nnum"]
memos = [("memo","bmSch","bmSch_wf","bmKey"),("lmemo","lfSch","lfSch_wf","lfKey"),("imemo","imSch","imSch_wf","lfKey")]
out = []
P = out.append
P("import ConAgua.Arena.ArenaRel\nimport ConAgua.Arena.WalkRefine\n")
P("/-! Spike (lane `scale`): " + mode + " relation with %d dummy memo clauses. Not imported by `ConAgua`. -/\n" % ND)
P("open ConRon.Arena\nopen Std.WP\nset_option linter.unusedSimpArgs false\nset_option linter.unusedVariables false\nnamespace L.Arena.Spike\n")
for i in range(ND):
    P(f"def dS{i} : MemoSch := ⟨{100+i}, {100+2*i}⟩")
    P(f"theorem dS{i}_wf : dS{i}.WF := ⟨by decide, by decide⟩")
dnames = " ".join(f", dS{i}" for i in range(ND))
apart_base = "Apart, POOL, CTL, BMEMO, bmSch, LMEMO, lfSch, IMEMO, imSch, litSch, REC, SLOT, appSch, AREC, ASLOT, sortSch, SOREC, SOSLOT, constSch, CREC, CSLOT, letSch, LEREC, LESLOT, bvarSch, BREC, BSLOT, fvarSch, FVREC, FVSLOT, lamSch, LAREC, LASLOT, forallSch, FAREC, FASLOT, projSch, PJREC, PJSLOT, zeroSch, ZREC, ZSLOT, succSch, SREC, SSLOT, maxSch, MREC, MSLOT, imaxSch, IREC, ISLOT, paramSch, PREC, PSLOT, lsSch, LSREC, LSSLOT, nanonSch, NAREC, NASLOT, nstrSch, NSREC, NSSLOT, nnumSch, NNREC, NNSLOT"
P(f'macro "apart3" : tactic => `(tactic| simp [{apart_base}{dnames}])\n')
def dfield(i): return f"  d{i} : MemoRG dS{i} bmKey (·.toNat) m a.memos.fvarBC"
def dframe(i, hR, hf, ap): return f"by first | $t | exact memoRG_frame dS{i} dS{i}_wf bmKey _ _ _ (by {ap}) (by {ap}) _ _ {hf} _ ({hR}).d{i}"
# write structure explicitly
def realfields():
    tys = dict(lit="LitR",app="AppR",sort="SortR",const="ConstR",letE="LetR",bvar="BVarR",fvar="FVarR",lam="LamR",forallE="ForallR",proj="ProjR",zero="ZeroR",succ="SuccR",max="MaxR",imax="ImaxR",param="ParamR",ls="LsR",nanon="NAnonR",nstr="NStrR",nnum="NNumR")
    L = [f"  {r} : {tys[r]} m a" for r in real]
    L += ["  memo : MemoRG bmSch bmKey (·.toNat) m a.memos.bvarBC",
          "  lmemo : MemoRG lfSch lfKey decE m a.memos.liftC",
          "  imemo : MemoRG imSch lfKey decE m a.memos.inst1C"]
    return L
if mode == "flat":
    P("structure AR (m : Mem) (a : AState) : Prop where")
    for x in realfields(): P(x)
    for i in range(ND): P(dfield(i))
    lines = [f"    by first | $t | exact ($hR).{r}.frame _ _ _ _ $hf _ (by apart3)" for r in real]
    lines += [f"    by first | $t | exact memoRG_frame {s} {w} {k} _ _ _ (by apart3) (by apart3) _ _ $hf _ ($hR).{f}" for (f,s,w,k) in memos]
    lines += ["    " + dframe(i, "$hR", "$hf", "apart3") for i in range(ND)]
    P('\nmacro "ab3 " hR:term ", " hf:term " with " t:tacticSeq : tactic => `(tactic| exact ⟨\n' + ",\n".join(lines) + "⟩)\n")
    R = "AR"; build = "ab3"
    def mk(hR): return hR
elif mode == "base":
    R = "ArenaR"; build = "arena_build"
elif mode == "nested":
    # groups of 22 dummy fields
    G = (ND + 21)//22
    for g in range(G):
        idx = list(range(22*g, min(ND, 22*g+22)))
        P(f"structure Grp{g} (m : Mem) (mp : Std.HashMap EIdx Nat) : Prop where")
        for i in idx: P(f"  d{i} : MemoRG dS{i} bmKey (·.toNat) m mp")
        lo, hi = 100 + idx[0], 100 + idx[-1] + 1
        clo, chi = 100 + 2*idx[0], 100 + 2*idx[-1] + 2
        P(f"\ntheorem Grp{g}.frame (A : List ArrId) (C : List Word) (hA : ∀ b ∈ A, b < {lo} ∨ {hi} ≤ b)\n    (hC : ∀ x ∈ C, x.toNat < {clo} ∨ {chi} ≤ x.toNat) (m m' : Mem) (hf : MemFrame A C m m') (mp : Std.HashMap EIdx Nat)\n    (h : Grp{g} m mp) : Grp{g} m' mp :=")
        items = []
        for i in idx:
            items.append(f"  memoRG_frame dS{i} dS{i}_wf bmKey _ _ _ (fun hm => by have := hA _ hm; simp [dS{i}] at this) (fun hm => by have := hC _ hm; simp [dS{i}] at this) _ _ hf _ h.d{i}")
        P("  ⟨" + ",\n".join(items).strip() + "⟩\n")
    P("structure AR (m : Mem) (a : AState) : Prop where\n  core : ArenaR m a")
    for g in range(G): P(f"  g{g} : Grp{g} m a.memos.fvarBC")
    R = "AR"; build = None
P("")
# lemmas
lifts = [("app","AppR","appSch","appLens"),("sort","SortR","sortSch","sortLens"),("const","ConstR","constSch","constLens"),("letE","LetR","letSch","letLens"),("bvar","BVarR","bvarSch","bvarLens")]
for (n,ty,sch,lens) in lifts:
    hdr = f"""theorem lift_{n} (m m' : Mem) (a a' : AState) (hR : {R} m a) (hX : {ty} m' a')
    (hf : MemFrame [{sch}.ra, {sch}.sa] [{sch}.ca, {sch}.ca + 1] m m')
    (hst : a' = a ∨ (∃ t, a' = {lens}.setP a t) ∨ (∃ t, a' = {lens}.setS a t)) : {R} m' a' := by"""
    if mode == "nested":
        P(hdr + f"\n  refine ⟨ArenaR.lift_{n} m m' a a' hR.core hX hf hst" + "".join(f", ?_" for g in range(G)) + "⟩")
        for g in range(G):
            P(f"  · rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> exact Grp{g}.frame _ _ (by apart3) (by apart3) m m' hf _ hR.g{g}")
    else:
        P(hdr + f"\n  rcases hst with rfl | ⟨t, rfl⟩ | ⟨t, rfl⟩ <;> {build} hR, hf with exact hX")
    P("")
# memo set / clear
ms = """theorem memo_set (m m' : Mem) (a : AState) (hR : {R} m a) (k v : Word)
    (hk : k.toNat < 2 ^ 32) (hs : msetG bmSch m k 0 v = some m') :
    {R} m' (withBC a (a.memos.bvarBC.insert (decE k) v.toNat)) := by
  have hf := msetG_frame bmSch bmSch_wf m m' k 0 v hs
"""
mc = """theorem memo_clear (m : Mem) (a : AState) (hR : {R} m a)
    (h0 : rdW (m.arr64 CTL) 24 + 2 ≠ 0) : {R} (mclearG bmSch m) (withBC a ∅) := by
  have hf := mclearG_frame bmSch m
"""
gr = """theorem grow (m m' : Mem) (hg : Grows m m') (a : AState) (hR : {R} m a) : {R} m' a := by
  have hf := grows_frame m m' hg
"""
if mode == "nested":
    P(ms.format(R=R) + "  exact ⟨ArenaR.memo_set m m' a hR.core k v hk hs" + "".join(f", Grp{g}.frame _ _ (by simp [bmSch, BMEMO]) (by simp [bmSch]) m m' hf _ hR.g{g}" for g in range(G)) + "⟩\n")
    P(mc.format(R=R) + "  exact ⟨ArenaR.memo_clear m a hR.core h0" + "".join(f", Grp{g}.frame _ _ (by simp [bmSch, BMEMO]) (by simp [bmSch]) m _ hf _ hR.g{g}" for g in range(G)) + "⟩\n")
    P(gr.format(R=R) + "  exact ⟨ArenaR.grow m m' hg a hR.core" + "".join(f", Grp{g}.frame _ _ (by simp [POOL]) (by simp) m m' hf _ hR.g{g}" for g in range(G)) + "⟩\n")
else:
    P(ms.format(R=R) + f"  {build} hR, hf with exact memoRG_set bmSch bmSch_wf bmKey _ m _ hR.memo k 0 v ⟨hk, rfl⟩ m' hs\n")
    P(mc.format(R=R) + f"  {build} hR, hf with exact memoRG_clear bmSch bmSch_wf bmKey _ m _ hR.memo h0\n")
    P(gr.format(R=R) + f"  {build} hR, hf with\n    first | exact LitR.grow m m' hg a hR.lit | exact LsR.grow m m' hg a hR.ls |\n      exact NStrR.grow m m' hg a hR.nstr\n")
P("end L.Arena.Spike")
print("\n".join(out))
