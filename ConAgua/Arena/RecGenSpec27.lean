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
  · rw [set64IW_get]; rw [if_neg (by omega)]
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
    rw [if_neg (by omega)]
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
  simp only [cosK]; rw [if_pos h]
theorem cosK_oob (h : ¬ (qo + j).toNat < (m.arr64 IW).size) : cosK qo j rest (some (r, m)) = none := by
  simp only [cosK]; rw [if_neg h]
theorem cosW_exit (h : ¬ j < al) : cosW p (k + 1) m vis q fto ftl rd mo ml c ao al qo j = some m := by
  simp only [cosW]; rw [if_neg h]
theorem cosW_step (h : j < al) : cosW p (k + 1) m vis q fto ftl rd mo ml c ao al qo j =
    cosK qo j (fun m' => cosW p k m' vis q fto ftl rd mo ml c ao al qo (j + 1))
      (callW p k "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, rdW (m.arr64 IW) (ao + j)] m) := by
  simp only [cosW]; rw [if_pos h]
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

attribute [ind_grind] cosK_ok cosK_oob cosW_exit cosW_step cosK2_some cosK1_some cosF_eq

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

/-- **`class_ctors_of`' loop refines `classCtorsOf`** on the constructors from slot `j`, the
written prefix `acc` of the slots carried. -/
theorem cosW_ok (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m0 cAs) (hlp : CtorsLp m0 ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64) (hq : qo.toNat = iwTop m0)
    (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (j : Word) (acc : List ClassCtor) (ps : List Nat),
    cosW p k m vis q fto ftl rd mo ml c ao al qo j = some m' → StageR dn vis fe m a → IWGrow m0 m →
    KeepW m0 m → iwTop m0 + al.toNat ≤ iwTop m → j ≤ al → decNL m qo.toNat j.toNat = some ps →
    FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p) m x) ps acc → RcMR m →
    ∃ xs a', (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat (cAs.drop j.toNat)).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧ KeepW m0 m' ∧ iwTop m0 + al.toNat ≤ iwTop m' ∧ RcMR m' ∧
      ∃ ps', decNL m' qo.toNat al.toNat = some ps' ∧
        FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p) m' x) ps' (acc ++ xs) := by
  have hcAs0 : decPL (truncM m0) (decCN (truncM m0)) ao.toNat al.toNat = some cAs := hcAs
  have hlen := decPL_length _ hcAs0
  induction k with
  | zero => intro m m' a j acc ps h; simp [cosW] at h
  | succ k ih =>
  intro m m' a j acc ps h hS hg hk htop hja hps hfa hP
  have hjk : j.toNat ≤ al.toNat := UInt64.le_iff_toNat_le.mp hja
  by_cases hj : j < al
  rotate_left
  · rw [cosW_exit (h := hj)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : al.toNat ≤ j.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hj
    have hje : j.toNat = al.toNat := by omega
    rw [List.drop_eq_nil_of_le (by omega)]
    refine ⟨[], a, rfl, hS, hg, hk, htop, hP, ps, by rw [← hje]; exact hps, by simpa using hfa⟩
  have hjl : j.toNat < al.toNat := UInt64.lt_iff_toNat_lt.mp hj
  have := al.toNat_lt
  have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [cosW_step (h := hj)] at h
  have hsz := hS.2.2.2.1
  -- the constructor record
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m0) hcAs0 j.toNat hjl
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hsz0 : (m0.arr64 IW).size < 2 ^ 64 := by omega
  have hrd0 := iwN_rdW_at (w := ao) (k := j.toNat) hv0 hsz0
  have hnj : ao + UInt64.ofNat j.toNat = ao + j := by simp
  rw [hnj] at hrd0
  have hT0 := (rdW (m0.arr64 CTL) 200).toNat_lt
  have hajt : (ao + j).toNat = ao.toNat + j.toNat := by
    simp only [iwTop] at hvt; rw [UInt64.toNat_add]; simp <;> omega
  have hrd : rdW (m.arr64 IW) (ao + j) = UInt64.ofNat v := by
    rw [rdW_grow hg (by rw [hajt]; exact hvt), hrd0.1]
  rw [hrd] at h
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd0.2
  have hcA0 : DecB (fun m => decCN m (UInt64.ofNat v : Word).toNat) m0 cAs[j.toNat] := by
    rw [hvT]; rw [← hlen] at hjl; exact hdv
  have hlp0 : CtorLp m0 (UInt64.ofNat v) := by
    have := hlp j.toNat hjl; rw [hnj, hrd0.1] at this; exact this
  -- `class_ctor_of`
  cases c1 : callW p k "class_ctor_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat v] m with
  | none => rw [c1] at h; simp [cosK] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [c1] at h
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hd1, hP1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classCtorOf_refines P.toCxoProg k _ a dn fe vis q fto ftl rd mo ml c (UInt64.ofNat v) bs formerTys R ms
      cAs[j.toNat] hS (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft) (Nat.le_trans hftb hg.1)
      (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg) hmsb
      (hcA0.grow (decCN_mono _) hg) (hlp0.grow hcA0 hsz0 hg hk) hnpk (by rw [hk IW]; exact hsz5) hP) c1
  simp only at hs1 hS1 hg1 hd1 hP1; subst hs1
  have run1 := AM.run_of_ok _ a hok1
  generalize hx1 : AM.res (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cAs[j.toNat]) a = x1 at run1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classCtorOf V fe bs formerTys R ms c.toNat cAs[j.toNat]) a = a1 at run1 hS1
  have hk1 := callW_keepW c1
  -- the slot write
  have hsz1 := hS1.2.2.2.1
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqj : (qo + j).toNat = qo.toNat + j.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hqb : (qo + j).toNat < (s1.mem.arr64 IW).size := by
    have := hS1.2.1; have := hg1.1; omega
  rw [cosK_ok (h := hqb)] at h
  have hb0 : iwTop m0 + al.toNat ≤ iwTop m := htop
  have hS2 := hS1.set_iw (qo + j) (r1.headD 0)
  have hg2 : IWGrow m0 (s1.mem.set64 IW (qo + j) (r1.headD 0)) := (hg.trans hg1).set_iw _ _ (by omega)
  have hk2 : KeepW m0 (s1.mem.set64 IW (qo + j) (r1.headD 0)) := (hk.trans hk1).set64 _ _ _
  have hA2 : AgreeA (iwTop m0 + al.toNat) s1.mem (s1.mem.set64 IW (qo + j) (r1.headD 0)) :=
    AgreeA.set_iw _ _ (by omega)
  have hps1 : decNL s1.mem qo.toNat j.toNat = some ps := by
    rw [decNL_grow hg1 (by omega)]; exact hps
  have hps2 := decNL_write s1.mem qo.toNat j.toNat (qo + j) (r1.headD 0) ps hqj (by omega) hps1
  have hfa2 : FA2 (fun p x => StabA (iwTop m0 + al.toNat) (fun m => decCC m p)
      (s1.mem.set64 IW (qo + j) (r1.headD 0)) x) (ps ++ [(r1.headD 0).toNat]) (acc ++ [x1]) :=
    FA2.snoc (FA2.imp (fun _ _ hq => (hq.grow (AgreeA.of_grow hg1)).grow hA2) hfa)
      ((hd1.mono hb0).grow hA2)
  obtain ⟨xs, a', run2, hS', hg', hk', ht', hP', ps', hps', hfa'⟩ := ih _ m' a1 (j + 1) (acc ++ [x1])
    (ps ++ [(r1.headD 0).toNat]) h hS2 hg2 hk2 (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg1.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [hj1]; exact hps2) hfa2 (hP1.fr (MFr.set_iw _ _ _))
  refine ⟨x1 :: xs, a', ?_, hS', hg', hk', ht', hP', ps', hps', by simpa using hfa'⟩
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classCtorsOf]
  rw [hj1] at run2
  simp only [StateT.run_bind, run1, except_ok_bind, run2]
  rfl

end cos

section cosf
variable {p : Prog} (P : CosProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include P

/-- **`class_ctors_of` refines `classCtorsOf`**: the constructors' records a slice stable above the
entry's top. -/
theorem cosF_ok (n : Nat) {m m' : Mem} {a : AState} {vis q fto ftl rd mo ml c ao al : Word} {r : List Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    {cAs : List (IConstantVal × Nat)}
    (h : cosF p n m vis q fto ftl rd mo ml c ao al = some (r, m')) (hS : StageR dn vis fe m a)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) m cAs) (hlp : CtorsLp m ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR m) :
    ∃ xs a', (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs).run a = .ok (xs, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      SPLA (iwTop m) decCC m' (r.headD 0).toNat (r.tail.headD 0).toNat xs ∧ RcMR m' := by
  rw [cosF_eq] at h
  cases hal : allocW m al with
  | none => rw [hal] at h; cases h
  | some x =>
  obtain ⟨qo, m1⟩ := x
  rw [hal, cosK1_some] at h
  cases hl : cosW p (n + 1) m1 vis q fto ftl rd mo ml c ao al qo 0 with
  | none => rw [hl] at h; cases h
  | some m2 =>
  rw [hl, cosK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hS
  have hf1 := allocW_mfr hal
  obtain ⟨xs, a', run, hS', hg', -, ht', hP', ps', hps', hfa'⟩ := cosW_ok P dn fe vis q fto ftl rd mo ml c ao al qo
    bs formerTys R ms cAs m hbs hft hftb hR hms hmsb hcAs hlp hnpk hsz5 hq (n + 1) m1 m2 a 0 [] [] hl hS1 hg1
    (KeepW.of_mfr hf1) (by omega) UInt64.zero_le (by simp [decNL]) .nil (hP.fr hf1)
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hfa'
  refine ⟨xs, a', run, hS', hg', ⟨.inr (by simp; omega), by simp; omega, ps', hps',
    FA2.imp (fun _ _ hq => hq.mono (by omega)) hfa'⟩, hP'⟩

end cosf

/-- **`class_ctors_of` refines `classCtorsOf`** (through `class_ctor_of`'s stubs and contracts):
`class_ctor_of`'s hypotheses, the constructors a pointer slice decoded below the tops with
`CtorLp` at each; the records a slice stable above the entry's top (`SPLA`). Under `StageR`; the
census link is `classCtorsOf_refinesC` (`IndT/RecGen27`). -/
theorem classCtorsOf_refines {p : Prog} (P : CosProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl rd mo ml c ao al : Word) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor) (cAs : List (IConstantVal × Nat))
    (hS : StageR dn vis fe s₀.mem a₀) (hbs : BSOK s₀.mem q.toNat bs)
    (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys) (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem)
    (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hcAs : DecB (fun m => decPL m (decCN m) ao.toNat al.toNat) s₀.mem cAs) (hlp : CtorsLp s₀.mem ao al)
    (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, ao, al]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      SPLA (iwTop s₀.mem) decCC s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat
        (AM.res (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat cAs) a₀) ∧ RcMR s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  refine triple_post (cos_spec p P.ha P.cos n s₀ vis q fto ftl rd mo ml c ao al) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xs, a', run, hS', hg, hd, hP'⟩ := cosF_ok P dn fe n hm hS hbs hft hftb hR hms hmsb hcAs hlp hnpk hsz5 hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd, hP'⟩

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
  simp only [ccsK2]; rw [if_pos h]
theorem ccsK2_oob (h : ¬ (qo + c).toNat < (m.arr64 IW).size) : ccsK2 qo c rest (some (r, m)) = none := by
  simp only [ccsK2]; rw [if_neg h]
theorem ccsK1_some : ccsK1 p k qo c rest (some (r, m)) =
    ccsK2 qo c rest (callW p k "rec2" [r.headD 0, r.tail.headD 0] m) := rfl
theorem ccsW_exit (h : ¬ c < ml) : ccsW p (k + 1) m vis q fto ftl rd mo ml qo c = some m := by
  simp only [ccsW]; rw [if_neg h]
theorem ccsW_step (h : c < ml) : ccsW p (k + 1) m vis q fto ftl rd mo ml qo c =
    ccsK1 p k qo c (fun m' => ccsW p k m' vis q fto ftl rd mo ml qo (c + 1))
      (callW p k "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c,
        rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + c) + 6), rdW (m.arr64 IW) (rdW (m.arr64 IW) (mo + c) + 7)] m) := by
  simp only [ccsW]; rw [if_pos h]
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

attribute [ind_grind] ccsK2_ok ccsK2_oob ccsK1_some ccsW_exit ccsW_step ccsK4_some ccsK3_some ccsF_eq

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

/-- **`classes_ctors`' loop refines `classesCtors`** on the classes from `c`, the written prefix
`acc` of the slots carried. -/
theorem ccsW_ok (hbs : BSOK m0 q.toNat bs) (hft : decHL m0 fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m0) (hR : DecB (fun m => decCR m rd.toNat) m0 R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m0 ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp m0 mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m0.arr64 IW).size + 5 < 2 ^ 64)
    (hq : qo.toNat = iwTop m0) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (c : Word) (acc : List (List ClassCtor)) (ps : List Nat),
    ccsW p k m vis q fto ftl rd mo ml qo c = some m' → StageR dn vis fe m a → IWGrow m0 m →
    KeepW m0 m → iwTop m0 + ml.toNat ≤ iwTop m → c ≤ ml → decNL m qo.toNat c.toNat = some ps →
    FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p) m x) ps acc →
    RcMR m →
    ∃ xss a', (ConRon.Arena.classesCtors V fe bs formerTys R ms c.toNat (ms.drop c.toNat)).run a =
        .ok (xss, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m0 m' ∧ KeepW m0 m' ∧ iwTop m0 + ml.toNat ≤ iwTop m' ∧ RcMR m' ∧
      ∃ ps', decNL m' qo.toNat ml.toNat = some ps' ∧
        FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p) m' x) ps'
          (acc ++ xss) := by
  have hms0 : decPL (truncM m0) (decTM (truncM m0)) mo.toNat ml.toNat = some ms := hms
  have hlen := decPL_length _ hms0
  have hsz0 : (m0.arr64 IW).size < 2 ^ 64 := by omega
  induction k with
  | zero => intro m m' a c acc ps h; simp [ccsW] at h
  | succ k ih =>
  intro m m' a c acc ps h hS hg hk htop hcm hps hfa hP
  have hck : c.toNat ≤ ml.toNat := UInt64.le_iff_toNat_le.mp hcm
  by_cases hc : c < ml
  rotate_left
  · rw [ccsW_exit (h := hc)] at h
    simp only [Option.some.injEq] at h; subst h
    have h1 : ml.toNat ≤ c.toNat := by simpa [UInt64.lt_iff_toNat_lt] using hc
    have hce : c.toNat = ml.toNat := by omega
    rw [List.drop_eq_nil_of_le (by omega)]
    refine ⟨[], a, ?_, hS, hg, hk, htop, hP, ps, by rw [← hce]; exact hps, by simpa using hfa⟩
    simp only [ConRon.Arena.classesCtors]; rfl
  have hcl : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hc
  have := ml.toNat_lt
  have hc1 : (c + 1).toNat = c.toNat + 1 := by rw [UInt64.toNat_add]; simp <;> omega
  rw [ccsW_step (h := hc)] at h
  -- the class record and its constructors
  obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m0) hms0 c.toNat hcl
  obtain ⟨hvt, hv0⟩ := rec2IwN_trunc hv
  have hrd0 := iwN_rdW_at (w := mo) (k := c.toNat) hv0 hsz0
  have hnc : mo + UInt64.ofNat c.toNat = mo + c := by simp
  rw [hnc] at hrd0
  have hmc : (mo + c).toNat < iwTop m0 := by rw [UInt64.toNat_add]; simp; omega
  have hrd : rdW (m.arr64 IW) (mo + c) = UInt64.ofNat v := by rw [rdW_grow hg hmc, hrd0.1]
  have hvT : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd0.2
  have hTM0 : DecB (fun m => decTM m v) m0 ms[c.toNat] := by rw [← hlen] at hcl; exact hdv
  obtain ⟨o, l, ho, hl, hv7, hcts⟩ := decTM_ctors hTM0
  have r6 := iwN_rdW_at (w := UInt64.ofNat v) (k := 6) (by rw [hvT]; exact ho) hsz0
  have r7 := iwN_rdW_at (w := UInt64.ofNat v) (k := 7) (by rw [hvT]; exact hl) hsz0
  simp only [show UInt64.ofNat 6 = (6 : Word) from rfl, show UInt64.ofNat 7 = (7 : Word) from rfl] at r6 r7
  have hv6t : (UInt64.ofNat v + 6 : Word).toNat < iwTop m0 := by rw [UInt64.toNat_add, hvT]; simp; omega
  have hv7t : (UInt64.ofNat v + 7 : Word).toNat < iwTop m0 := by rw [UInt64.toNat_add, hvT]; simp; omega
  rw [hrd, rdW_grow hg hv6t, rdW_grow hg hv7t, r6.1, r7.1] at h
  have hoT : (UInt64.ofNat o : Word).toNat = o := UInt64.toNat_ofNat_of_lt' r6.2
  have hlT : (UInt64.ofNat l : Word).toNat = l := UInt64.toNat_ofNat_of_lt' r7.2
  have hcts' : DecB (fun m => decPL m (decCN m) (UInt64.ofNat o : Word).toNat (UInt64.ofNat l : Word).toNat) m0
      ms[c.toNat].ctors := by rw [hoT, hlT]; exact hcts
  have hlp0 := hlp c.toNat hcl v o l hv0 ho hl
  have hol : (UInt64.ofNat o : Word).toNat + (UInt64.ofNat l : Word).toNat < 2 ^ 64 := by
    rcases decB_decPL_bound hcts with h0 | h0
    · rw [hoT, hlT, h0]; omega
    · rw [hoT, hlT]; have := (rdW (m0.arr64 CTL) 200).toNat_lt; simp only [iwTop] at h0; omega
  -- `class_ctors_of`
  cases c1 : callW p k "class_ctors_of" [vis, q, fto, ftl, rd, mo, ml, c, UInt64.ofNat o, UInt64.ofNat l] m with
  | none => rw [c1] at h; simp [ccsK1] at h
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [c1, ccsK1_some] at h
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hd1, hP1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classCtorsOf_refines P.toCosProg k _ a dn fe vis q fto ftl rd mo ml c (UInt64.ofNat o) (UInt64.ofNat l) bs
      formerTys R ms ms[c.toNat].ctors hS (hbs.grow hg) (by rw [decHL_grow hg hftb]; exact hft)
      (Nat.le_trans hftb hg.1) (hR.grow (decCR_mono _) hg) (hms.grow (OMono.decPL (fun q => decTM_mono q) _ _) hg)
      hmsb (hcts'.grow (OMono.decPL (fun q => decCN_mono q) _ _) hg) (hlp0.grow hcts' hsz0 hg hk) hnpk
      (by rw [hk IW]; exact hsz5) hP) c1
  simp only at hs1 hS1 hg1 hd1 hP1; subst hs1
  have run1 := AM.run_of_ok _ a hok1
  generalize hx1 : AM.res (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat ms[c.toNat].ctors) a = x1 at run1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classCtorsOf V fe bs formerTys R ms c.toNat ms[c.toNat].ctors) a = a1 at run1 hS1
  have hk1 := callW_keepW c1
  -- `rec2`
  cases c2 : callW p k "rec2" [r1.headD 0, r1.tail.headD 0] s1.mem with
  | none => rw [c2] at h; simp [ccsK2] at h
  | some x2 =>
  obtain ⟨r2, m2⟩ := x2
  rw [c2] at h
  obtain ⟨s2, hs2, -, hw2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (rec2_specW p P.ha k P.r2 _ (r1.headD 0) (r1.tail.headD 0)) c2
  simp only at hs2 hw2; subst hs2
  have hsz1 := hS1.2.2.2.1
  obtain ⟨hr2, hget2, hg2, hf2, ht2, hroom2⟩ := recW_post hw2 hS1.2.2.2.2.2 hsz1 rfl
  have hS2 := stage_frame_iw hS1 hf2 (by simp at ht2 hroom2; omega)
  have hk2 : KeepW s1.mem s2.mem := KeepW.of_mfr (MFr.of_iw hf2)
  have hP2 := hP1.fr (MFr.of_iw hf2)
  have hb0 : iwTop m0 + ml.toNat ≤ iwTop m := htop
  have hhdr : StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) (r2.headD 0).toNat) s2.mem x1 := by
    rw [hr2]
    have hw0 : iwN s2.mem (rdW (s1.mem.arr64 CTL) 200).toNat = some (r1.headD 0).toNat := by
      have e0 := hget2 0 (by simp); rw [Nat.add_zero] at e0
      simp only [iwN, nat?, iwA, e0]; rfl
    have hw1 : iwN s2.mem ((rdW (s1.mem.arr64 CTL) 200).toNat + 1) = some (r1.tail.headD 0).toNat := by
      have e1 := hget2 1 (by simp)
      simp only [iwN, nat?, iwA, e1]; rfl
    have ht2' : iwTop s2.mem = iwTop s1.mem + 2 := by simpa using ht2
    exact stabA_decLH hw0 hw1 (Nat.le_trans hb0 hg1.1) (by rw [ht2']; exact Nat.le_refl _)
      ((hd1.mono (by omega)).grow (AgreeA.of_grow hg2))
  -- the slot write
  have hTm := hS.lt64 (Nat.le_refl (iwTop m))
  have hqc : (qo + c).toNat = qo.toNat + c.toNat := by rw [UInt64.toNat_add]; simp <;> omega
  have hqb : (qo + c).toNat < (s2.mem.arr64 IW).size := by
    have := hS2.2.1; have := hg1.1; have := hg2.1; omega
  rw [ccsK2_ok (h := hqb)] at h
  have hg12 := hg1.trans hg2
  have hS3 := hS2.set_iw (qo + c) (r2.headD 0)
  have hg3 : IWGrow m0 (s2.mem.set64 IW (qo + c) (r2.headD 0)) := ((hg.trans hg12)).set_iw _ _ (by omega)
  have hk3 : KeepW m0 (s2.mem.set64 IW (qo + c) (r2.headD 0)) := (hk.trans (hk1.trans hk2)).set64 _ _ _
  have hA3 : AgreeA (iwTop m0 + ml.toNat) s2.mem (s2.mem.set64 IW (qo + c) (r2.headD 0)) :=
    AgreeA.set_iw _ _ (by omega)
  have hps2 : decNL s2.mem qo.toNat c.toNat = some ps := by rw [decNL_grow hg12 (by omega)]; exact hps
  have hps3 := decNL_write s2.mem qo.toNat c.toNat (qo + c) (r2.headD 0) ps hqc (by omega) hps2
  have hfa3 : FA2 (fun p x => StabA (iwTop m0 + ml.toNat) (fun m => decLH m (decPL m (decCC m)) p)
      (s2.mem.set64 IW (qo + c) (r2.headD 0)) x) (ps ++ [(r2.headD 0).toNat]) (acc ++ [x1]) :=
    FA2.snoc (FA2.imp (fun _ _ hq => (hq.grow (AgreeA.of_grow hg12)).grow hA3) hfa) (hhdr.grow hA3)
  obtain ⟨xss, a', run2, hS', hg', hk', ht', hP', ps', hps', hfa'⟩ := ih _ m' a1 (c + 1) (acc ++ [x1])
    (ps ++ [(r2.headD 0).toNat]) h hS3 hg3 hk3
    (by rw [iwTop_set_iw]; exact Nat.le_trans htop hg12.1)
    (UInt64.le_iff_toNat_le.mpr (by omega)) (by rw [hc1]; exact hps3) hfa3 (hP2.fr (MFr.set_iw _ _ _))
  refine ⟨x1 :: xss, a', ?_, hS', hg', hk', ht', hP', ps', hps', by simpa using hfa'⟩
  rw [List.drop_eq_getElem_cons (by omega), ConRon.Arena.classesCtors]
  rw [hc1] at run2
  simp only [StateT.run_bind, run1, except_ok_bind, run2]
  rfl

end ccs

section ccsf
variable {p : Prog} (P : CcsProg p) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv)
include P

/-- **`classes_ctors` refines `classesCtors`**: every class's constructors under a fresh header,
the headers a slice stable above the entry's top. -/
theorem ccsF_ok (n : Nat) {m m' : Mem} {a : AState} {vis q fto ftl rd mo ml : Word} {r : List Word}
    {bs : BlockShape} {formerTys : List EIdx} {R : ClassRead} {ms : List TargetMajor}
    (h : ccsF p n m vis q fto ftl rd mo ml = some (r, m')) (hS : StageR dn vis fe m a)
    (hbs : BSOK m q.toNat bs) (hft : decHL m fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop m) (hR : DecB (fun m => decCR m rd.toNat) m R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp m mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64) (hsz5 : (m.arr64 IW).size + 5 < 2 ^ 64)
    (hP : RcMR m) :
    ∃ xss a', (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms).run a = .ok (xss, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      SPLA (iwTop m) (fun m p => decLH m (decPL m (decCC m)) p) m' (r.headD 0).toNat (r.tail.headD 0).toNat xss ∧
      RcMR m' := by
  rw [ccsF_eq] at h
  cases hal : allocW m ml with
  | none => rw [hal] at h; cases h
  | some x =>
  obtain ⟨qo, m1⟩ := x
  rw [hal, ccsK3_some] at h
  cases hl : ccsW p (n + 1) m1 vis q fto ftl rd mo ml qo 0 with
  | none => rw [hl] at h; cases h
  | some m2 =>
  rw [hl, ccsK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hS1, hg1, hq, ht1⟩ := allocW_stage hal hS
  have hf1 := allocW_mfr hal
  obtain ⟨xss, a', run, hS', hg', -, ht', hP', ps', hps', hfa'⟩ := ccsW_ok P dn fe vis q fto ftl rd mo ml qo
    bs formerTys R ms m hbs hft hftb hR hms hmsb hlp hnpk hsz5 hq (n + 1) m1 m2 a 0 [] [] hl hS1 hg1
    (KeepW.of_mfr hf1) (by omega) UInt64.zero_le (by simp [decNL]) .nil (hP.fr hf1)
  simp only [UInt64.toNat_zero, List.drop_zero, List.nil_append] at run hfa'
  refine ⟨xss, a', run, hS', hg', ⟨.inr (by simp; omega), by simp; omega, ps', hps',
    FA2.imp (fun _ _ hq => hq.mono (by omega)) hfa'⟩, hP'⟩

end ccsf

/-- **`classes_ctors` refines `classesCtors`** (through `class_ctor_of`'s stubs and contracts): the
class's shape (`BSOK`, parameter count plus member count word-sized), former types, the class
reading and the classes decoded below the tops, `CtorLp` at every class's every constructor
(`ClassesLp`), the pool's size `+ 5` word-sized, the walk memos well formed; each class's
constructors under a `[off, len]` header, the headers a slice stable above the entry's top. -/
@[refines ConRon.Arena.classesCtors]
theorem classesCtors_refines {p : Prog} (P : CcsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis q fto ftl rd mo ml : Word) (bs : BlockShape)
    (formerTys : List EIdx) (R : ClassRead) (ms : List TargetMajor) (hS : StageR dn vis fe s₀.mem a₀)
    (hbs : BSOK s₀.mem q.toNat bs) (hft : decHL s₀.mem fto.toNat ftl.toNat = some formerTys)
    (hftb : fto.toNat + ftl.toNat ≤ iwTop s₀.mem) (hR : DecB (fun m => decCR m rd.toNat) s₀.mem R)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) s₀.mem ms) (hmsb : mo.toNat + ml.toNat < 2 ^ 64)
    (hlp : ClassesLp s₀.mem mo ml) (hnpk : bs.nP + bs.k < 2 ^ 64)
    (hsz5 : (s₀.mem.arr64 IW).size + 5 < 2 ^ 64) (hP : RcMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "classes_ctors" [vis, q, fto, ftl, rd, mo, ml]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      SPLA (iwTop s₀.mem) (fun m p => decLH m (decPL m (decCC m)) p) s'.mem (r.headD 0).toNat
        (r.tail.headD 0).toNat (AM.res (ConRon.Arena.classesCtors V fe bs formerTys R ms 0 ms) a₀) ∧
      RcMR s'.mem; ⊤⦄ := by
  cases n with
  | zero => exact triple_post (invoke_exec_zero p _ _ _) (fun _ _ h => h.elim)
  | succ n =>
  refine triple_post (ccs_spec p P.ha P.ccs n s₀ vis q fto ftl rd mo ml) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨xss, a', run, hS', hg, hd, hP'⟩ := ccsF_ok P dn fe n hm hS hbs hft hftb hR hms hmsb hlp hnpk hsz5 hP
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hd, hP'⟩

end L.Ind
