import ConAgua.Arena.RecGenSpec26

/-!
# `classCtorsOf`, `classesCtors` (lane `indproofs4`, helper `cls`)

`class_ctors_of(vis, p, ft.off, ft.len, rd, ms.off, ms.len, c, cAs.off, cAs.len)`: every
constructor of class `c`, each `class_ctor_of` record written into a slot of a slice allocated
first; `classes_ctors(vis, p, ft.off, ft.len, rd, ms.off, ms.len)`: every class's constructors,
each class's slice under a fresh `rec2` header written into a slot. Both loops are named blocks
(`cosLoop`, `ccsLoop`) with models (`cosW`, `ccsW`) and relational lemmas by induction on the loop
fuel, carrying the written prefix of the slots.

**Writes below the top.** A slot is written after the records it points to were made, below the
top: no pool growth. What is made after the allocation reads only words from the slots' end on
(`StabA`, `SPLA`: `class_ctor_of` and `class_fields_of` return such decodings), and a slot write
keeps every word from there on (`AgreeA.set_iw`); the inputs, decoded below the top at the
allocation, keep growing (`IWGrow.set_iw`).

**`CtorLp`** (`target_ctor_at`'s level-parameter slice in `EREC`) is a hypothesis per constructor
record; it holds whenever the slice is nonempty (its decoding reads it), and for an empty slice
whenever its offset is below `EREC`'s size.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Tools -/

theorem AgreeA.set_iw {b : Nat} (m : Mem) {i : Word} (v : Word) (hi : i.toNat < b) :
    AgreeA b m (m.set64 IW i v) := by
  refine ⟨by rw [iwTop_set_iw]; exact Nat.le_refl _,
    by simp only [erTop]; rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact Nat.le_refl _,
    fun j hj _ => ?_, fun j _ => ?_⟩
  · rw [set64IW_get]; rw [ite_eq_right (by omega)]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]

theorem KeepW.of_mfr {S : List ArrId} {T : List Word} {m m' : Mem} (h : MFr S T m m') : KeepW m m' := by
  obtain ⟨A, C, hf, -, -⟩ := h
  exact hf.2.2.1

/-- `CtorLp` holds on as the pools grow and keep their sizes. -/
theorem CtorLp.grow {m m' : Mem} {cA : Word} {x : IConstantVal × Nat} (h : CtorLp m cA)
    (hcA : DecB (fun m => decCN m cA.toNat) m x) (hsz : (m.arr64 IW).size < 2 ^ 64) (hg : IWGrow m m')
    (hk : KeepW m m') : CtorLp m' cA := by
  obtain ⟨a, ha, ha3, -, -, -, -, -, hct⟩ := decCN_words hcA hsz
  have ha64 : a + 3 < 2 ^ 64 := by have := (rdW (m.arr64 CTL) 129).toNat_lt; simp only [erTop] at ha3; omega
  have e1 : (UInt64.ofNat a + 1 : Word).toNat = a + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  have e2 : (UInt64.ofNat a + 2 : Word).toNat = a + 2 := by rw [UInt64.toNat_add]; simp <;> omega
  simp only [CtorLp] at h ⊢
  rw [ha] at h
  rw [rdW_grow hg (by omega), ha]
  rw [rdW_er_grow hg (by rw [e2]; omega), rdW_er_grow hg (by rw [e1]; omega), hk EREC]
  exact h

theorem FA2.snoc {α β : Type} {R : α → β → Prop} :
    ∀ {as : List α} {bs : List β} {a : α} {b : β}, FA2 R as bs → R a b → FA2 R (as ++ [a]) (bs ++ [b])
  | _, _, _, _, .nil, h => .cons h .nil
  | _, _, _, _, .cons h1 h2, h => .cons h1 (FA2.snoc h2 h)

/-- A prefix of words written one after the other, the next one at its end. -/
theorem decNL_write (m : Mem) (o j : Nat) (w v : Word) (ps : List Nat) (hw : w.toNat = o + j)
    (hsz : o + j < (m.arr64 IW).size) (h : decNL m o j = some ps) :
    decNL (m.set64 IW w v) o (j + 1) = some (ps ++ [v.toNat]) := by
  rw [decNL_snoc]
  have e1 : decNL (m.set64 IW w v) o j = decNL m o j := by
    simp only [decNL]
    apply mapM_opt_congr
    intro i hi
    have hi' : i < j := List.mem_range.mp hi
    simp only [iwN, nat?, iwA, set64IW_get]
    rw [ite_eq_right (by omega)]
  rw [e1, h]
  simp [iwN, nat?, iwA, set64IW_get, hw, hsz]

/-! ## `class_ctors_of`: the loop as a named block -/

/-- The loop of `classCtorsOfL` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classCtorsOfL`'s own loop (`rfl`), a named block for the proof
def cosLoop : Stmt := lblk (vis, p, ftOff, ftLen, rd, msOff, msLen, c, cAsOff, cAsLen, q, j, cc) {
  while j < cAsLen {
    cc := call class_ctor_of(vis, p, ftOff, ftLen, rd, msOff, msLen, c, IW.u64[cAsOff + j]);
    IW.u64[q + j] := cc;
    j += 1
  }
}

/-- `classCtorsOfL`, with its loop spliced from `cosLoop`. -/
-- con-ron: none — `classCtorsOfL` itself (`rfl`), its loop a named block for the proof
def classCtorsOfL' : FunDecl := lfn (vis, p, ftOff, ftLen, rd, msOff, msLen, c, cAsOff, cAsLen)
    locals (q, j, cc) {
  q := call iw_alloc(cAsLen);
  j := 0;
  ⟪cosLoop⟫;
  return (q, cAsLen)
}

theorem classCtorsOfL_eq : classCtorsOfL = classCtorsOfL' := rfl

section model
variable (p : Prog)

/-- After `class_ctor_of`: the slot write, then the next constructor. -/
def cosK (qo j : Word) (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => if (qo + j).toNat < (m.arr64 IW).size then rest (m.set64 IW (qo + j) (r.headD 0)) else none

/-- **The model of `class_ctors_of`' loop** at L fuel `k`, from slot `j`: the memory at the exit. -/
def cosW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Option Mem
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, q, fto, ftl, rd, mo, ml, c, ao, al, qo, j =>
    if j < al then
      cosK qo j (fun m' => cosW k m' vis q fto ftl rd mo ml c ao al qo (j + 1))
        (callW p k "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, rdW (m.arr64 IW) (ao + j)] m)
    else some m

section arms
variable (k : Nat) (m : Mem) (vis q fto ftl rd mo ml c ao al qo j : Word) (r : List Word)
  (rest : Mem → Option Mem)
theorem cosK_ok (h : (qo + j).toNat < (m.arr64 IW).size) :
    cosK qo j rest (some (r, m)) = rest (m.set64 IW (qo + j) (r.headD 0)) := by
  simp only [cosK]; rw [ite_eq_left h]
theorem cosW_exit (h : ¬ j < al) : cosW p (k + 1) m vis q fto ftl rd mo ml c ao al qo j = some m := by
  simp only [cosW]; rw [ite_eq_right h]
theorem cosW_step (h : j < al) : cosW p (k + 1) m vis q fto ftl rd mo ml c ao al qo j =
    cosK qo j (fun m' => cosW p k m' vis q fto ftl rd mo ml c ao al qo (j + 1))
      (callW p k "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, rdW (m.arr64 IW) (ao + j)] m) := by
  simp only [cosW]; rw [ite_eq_left h]
end arms

/-- After the loop. -/
def cosK2 (qo al : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m => some ([qo, al], m)

/-- After the allocation: the loop. -/
def cosK1 (n : Nat) (vis q fto ftl rd mo ml c ao al : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (qo, m) => cosK2 qo al (cosW p (n + 1) m vis q fto ftl rd mo ml c ao al qo 0)

/-- **The model of `class_ctors_of`** (exec fuel `n + 1`). -/
def cosF (n : Nat) (m : Mem) (vis q fto ftl rd mo ml c ao al : Word) : Option (List Word × Mem) :=
  cosK1 p n vis q fto ftl rd mo ml c ao al (allocW m al)

theorem cosK2_some (qo al : Word) (m : Mem) : cosK2 qo al (some m) = some ([qo, al], m) := rfl
theorem cosK1_some (n : Nat) (vis q fto ftl rd mo ml c ao al qo : Word) (m : Mem) :
    cosK1 p n vis q fto ftl rd mo ml c ao al (some (qo, m)) =
      cosK2 qo al (cosW p (n + 1) m vis q fto ftl rd mo ml c ao al qo 0) := rfl
theorem cosF_eq (n : Nat) (m : Mem) (vis q fto ftl rd mo ml c ao al : Word) :
    cosF p n m vis q fto ftl rd mo ml c ao al = cosK1 p n vis q fto ftl rd mo ml c ao al (allocW m al) := rfl

end model

attribute [ind_grind] cosK_ok cosW_exit cosW_step cosK2_some cosK1_some cosF_eq

theorem cosLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k cosLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 10 = s₀.loc 10 ∧
      cosW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) (s₀.loc 9) (s₀.loc 10) (s₀.loc 11) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := cosLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64, ih,
        callW_spec p k "class_ctor_of"] <;>
      finish (gen := 40) (instances := 20000)

theorem cos_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "class_ctors_of" = some classCtorsOfL) (n : Nat) (s₀ : St)
    (vis q fto ftl rd mo ml c ao al : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, ao, al]
    ⦃fun r s' => LocEq s' s₀ ∧ cosF p n s₀.mem vis q fto ftl rd mo ml c ao al = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, classCtorsOfL_eq]
  simp only [callFn, classCtorsOfL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, iwAlloc_specW p ha n,
      fun s => Triple.step_exec (cosLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [loc_init4, loc_init5, loc_init6, loc_init7, loc_init8, loc_init9]

/-! ## `class_ctors_of`: the relational side -/

/-- The lookups of `class_ctors_of`. -/
structure CosProg (p : Prog) : Prop extends CxoProg p where
  cos : p.lookup "class_ctors_of" = some classCtorsOfL

/-- `CtorLp` at every constructor record of a slice. -/
def CtorsLp (m : Mem) (ao al : Word) : Prop :=
  ∀ j < al.toNat, CtorLp m (rdW (m.arr64 IW) (ao + UInt64.ofNat j))

section cos
variable {p : Prog} (P : CosProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl rd mo ml c ao al qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (cAs : List (IConstantVal × Nat)) (m0 : Mem)
include P

end cos

section cosf
variable {p : Prog} (P : CosProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include P

end cosf

/-! ## `classes_ctors`: the loop as a named block -/

/-- The loop of `classesCtorsL` (RecGen.lean), named for its spec. -/
-- con-ron: none — `classesCtorsL`'s own loop (`rfl`), a named block for the proof
def ccsLoop : Stmt := lblk (vis, p, ftOff, ftLen, rd, msOff, msLen, q, c, m, xsOff, xsLen, hdr) {
  while c < msLen {
    m := IW.u64[msOff + c];
    (xsOff, xsLen) := call class_ctors_of(vis, p, ftOff, ftLen, rd, msOff, msLen, c,
      IW.u64[m + 6], IW.u64[m + 7]);
    hdr := call rec2(xsOff, xsLen);
    IW.u64[q + c] := hdr;
    c += 1
  }
}

/-- `classesCtorsL`, with its loop spliced from `ccsLoop`. -/
-- con-ron: none — `classesCtorsL` itself (`rfl`), its loop a named block for the proof
def classesCtorsL' : FunDecl := lfn (vis, p, ftOff, ftLen, rd, msOff, msLen)
    locals (q, c, m, xsOff, xsLen, hdr) {
  q := call iw_alloc(msLen);
  c := 0;
  ⟪ccsLoop⟫;
  return (q, msLen)
}

theorem classesCtorsL_eq : classesCtorsL = classesCtorsL' := rfl

section model
variable (p : Prog)

/-- After `rec2`: the slot write, then the next class. -/
def ccsK2 (qo c : Word) (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => if (qo + c).toNat < (m.arr64 IW).size then rest (m.set64 IW (qo + c) (r.headD 0)) else none

/-- After `class_ctors_of`: the header. -/
def ccsK1 (k : Nat) (qo c : Word) (rest : Mem → Option Mem) : Option (List Word × Mem) → Option Mem
  | none => none
  | some (r, m) => ccsK2 qo c rest (callW p k "rec2" [r.headD 0, r.tail.headD 0] m)

/-- **The model of `classes_ctors`' loop** at L fuel `k`, from class `c`: the memory at the exit. -/
def ccsW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Option Mem
  | 0, _, _, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, q, fto, ftl, rd, mo, ml, qo, c =>
    if c < ml then
      ccsK1 p k qo c (fun m' => ccsW k m' vis q fto ftl rd mo ml qo (c + 1))
        (callW p k "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c,
          rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + c) + 6), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + c) + 7)] m)
    else some m

section arms
variable (k : Nat) (m : Mem) (vis q fto ftl rd mo ml qo c : Word) (r : List Word) (rest : Mem → Option Mem)
theorem ccsK2_ok (h : (qo + c).toNat < (m.arr64 IW).size) :
    ccsK2 qo c rest (some (r, m)) = rest (m.set64 IW (qo + c) (r.headD 0)) := by
  simp only [ccsK2]; rw [ite_eq_left h]
theorem ccsK1_some : ccsK1 p k qo c rest (some (r, m)) =
    ccsK2 qo c rest (callW p k "rec2" [r.headD 0, r.tail.headD 0] m) := rfl
theorem ccsW_exit (h : ¬ c < ml) : ccsW p (k + 1) m vis q fto ftl rd mo ml qo c = some m := by
  simp only [ccsW]; rw [ite_eq_right h]
theorem ccsW_step (h : c < ml) : ccsW p (k + 1) m vis q fto ftl rd mo ml qo c =
    ccsK1 p k qo c (fun m' => ccsW p k m' vis q fto ftl rd mo ml qo (c + 1))
      (callW p k "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c,
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + c) + 6), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + c) + 7)] m) := by
  simp only [ccsW]; rw [ite_eq_left h]
end arms

/-- After the loop. -/
def ccsK4 (qo ml : Word) : Option Mem → Option (List Word × Mem)
  | none => none
  | some m => some ([qo, ml], m)

/-- After the allocation: the loop. -/
def ccsK3 (n : Nat) (vis q fto ftl rd mo ml : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (qo, m) => ccsK4 qo ml (ccsW p (n + 1) m vis q fto ftl rd mo ml qo 0)

/-- **The model of `classes_ctors`** (exec fuel `n + 1`). -/
def ccsF (n : Nat) (m : Mem) (vis q fto ftl rd mo ml : Word) : Option (List Word × Mem) :=
  ccsK3 p n vis q fto ftl rd mo ml (allocW m ml)

theorem ccsK4_some (qo ml : Word) (m : Mem) : ccsK4 qo ml (some m) = some ([qo, ml], m) := rfl
theorem ccsK3_some (n : Nat) (vis q fto ftl rd mo ml qo : Word) (m : Mem) :
    ccsK3 p n vis q fto ftl rd mo ml (some (qo, m)) = ccsK4 qo ml (ccsW p (n + 1) m vis q fto ftl rd mo ml qo 0) := rfl
theorem ccsF_eq (n : Nat) (m : Mem) (vis q fto ftl rd mo ml : Word) :
    ccsF p n m vis q fto ftl rd mo ml = ccsK3 p n vis q fto ftl rd mo ml (allocW m ml) := rfl

end model

attribute [ind_grind] ccsK2_ok ccsK1_some ccsW_exit ccsW_step ccsK4_some ccsK3_some ccsF_eq

theorem ccsLoop_spec (p : Prog) (k : Nat) (s₀ : St) :
    ⦃fun s => s = s₀⦄ exec p k ccsLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
      ccsW p k s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 5) (s₀.loc 6)
        (s₀.loc 7) (s₀.loc 8) = some s'.mem; ⊤⦄ := by
  induction k generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ k ih =>
    rw [exec, step_while (w := ccsLoop) rfl]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64_rdW_spec, st64, ih,
        callW_spec p k "class_ctors_of", callW_spec p k "rec2"] <;>
      finish (gen := 40) (instances := 20000)

theorem ccs_spec (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hp : p.lookup "classes_ctors" = some classesCtorsL) (n : Nat) (s₀ : St) (vis q fto ftl rd mo ml : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "classes_ctors" [vis, q, fto, ftl, rd, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ ccsF p n s₀.mem vis q fto ftl rd mo ml = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp, classesCtorsL_eq]
  simp only [callFn, classesCtorsL']
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, iwAlloc_specW p ha n,
      fun s => Triple.step_exec (ccsLoop_spec p (n + 1) s)] <;>
    finish (gen := 40) (instances := 20000) [loc_init4, loc_init5, loc_init6]

/-! ## `classes_ctors`: the relational side -/

/-- A `TargetMajor` decoded below the tops: its constructors' slice (words 6, 7). -/
theorem decTM_ctors {m : Mem} {v : Nat} {M : TargetMajor} (h : DecB (fun m => decTM m v) m M) :
    ∃ o l : Nat, iwN m (v + 6) = some o ∧ iwN m (v + 7) = some l ∧ v + 7 < iwTop m ∧
      DecB (fun m => decPL m (decCN m) o l) m M.ctors := by
  have h' : decTM (truncM m) v = some M := h
  simp only [decTM, bind, Option.bind_eq_some_iff, pure] at h'
  obtain ⟨i, hi, lv, hlv, ds, hds, nPc, hnPc, nIdx, hnIdx, ctors, hctors, mem, hmem, nfs, hnfs, pf, hpf, hM⟩ := h'
  cases hM
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hctors
  obtain ⟨-, ho'⟩ := rec2IwN_trunc ho
  obtain ⟨hlt, hl'⟩ := rec2IwN_trunc hl
  exact ⟨o, l, ho', by simpa [Nat.add_assoc] using hl', by simpa [Nat.add_assoc] using hlt, hd⟩

/-- `CtorsLp` holds on as the pools grow and keep their sizes. -/
theorem CtorsLp.grow {m m' : Mem} {ao al : Word} {cAs : List (IConstantVal × Nat)} (h : CtorsLp m ao al)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m cAs) (hsz : (m.arr64 IW).size < 2 ^ 64)
    (hg : IWGrow m m') (hk : KeepW m m') : CtorsLp m' ao al := by
  intro j hj
  have hcAs0 : decPL (truncM m) (decCN (truncM m)) ao.toNat al.toNat = some cAs := hcAs
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hcAs0 j hj
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hrd := iwN_rdW_at (w := ao) (k := j) hv0 hsz
  have hgt : (ao + UInt64.ofNat j).toNat < iwTop m := by
    rw [UInt64.toNat_add]; simp; have := ao.toNat_lt; omega
  rw [rdW_grow hg hgt, hrd.1]
  have := h j hj
  rw [hrd.1] at this
  have hdv' : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m (cAs[j]'(by
      rw [decPL_length _ hcAs0]; exact hj)) := by
    rw [UInt64.toNat_ofNat_of_lt' hrd.2]; exact hdv
  exact this.grow hdv' hsz hg hk

/-- `CtorLp` at every constructor record of every class of `(ms.off, ms.len)`. -/
def ClassesLp (m : Mem) (mo ml : Word) : Prop :=
  ∀ c < ml.toNat, ∀ v o l, iwN m (mo.toNat + c) = some v → iwN m (v + 6) = some o → iwN m (v + 7) = some l →
    CtorsLp m (UInt64.ofNat o) (UInt64.ofNat l)

/-- A fresh `[off, len]` header (at or above `b`) of a slice stable above `b`. -/
theorem stabA_decLH {α : Type} {dec : Mem → Nat → Option α} {m : Mem} {hq o l b : Nat} {xs : List α}
    (h0 : iwN m hq = some o) (h1 : iwN m (hq + 1) = some l) (hb : b ≤ hq) (ht : hq + 2 ≤ iwTop m)
    (hs : SPLA b dec m o l xs) : StabA b (fun m => decLH m (decPL m (dec m)) hq) m xs := by
  intro m' hA
  simp only [decLH, decAt]
  rw [hA.iwN hb (by omega), h0, hA.iwN (by omega) (by omega), h1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact hs.stab m' hA

/-- The lookups of `classes_ctors`. -/
structure CcsProg (p : Prog) : Prop extends CosProg p where
  r2 : p.lookup "rec2" = some rec2
  ccs : p.lookup "classes_ctors" = some classesCtorsL

section ccs
variable {p : Prog} (P : CcsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
  (vis q fto ftl rd mo ml qo : Word) (bs : BlockShape) (formerTys : List EIdx) (R : ClassRead)
  (ms : List TargetMajor) (m0 : Mem)
include P

end ccs

section ccsf
variable {p : Prog} (P : CcsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include P

end ccsf

end L.Ind
