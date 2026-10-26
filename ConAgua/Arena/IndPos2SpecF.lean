import ConAgua.Arena.IndPosMemo
import ConAgua.Arena.RecCheckSpec
import ConAgua.Arena.StageInst1

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestHoles`,
`nestRootCanon`, … -/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `cv_lps` under the stage relation, an empty slice at any offset -/

theorem posmemo_cvLpsW_mfr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : cvLpsW n m q = some (r, m')) :
    MFr [] [] m m' := erToIwW_mfr h

theorem pos2_cvLpsW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {q : Word} {r : List Word} {cv : IConstantVal}
    (h : cvLpsW n m q = some (r, m')) (hS : StageR dn vis fe m a)
    (hcv : decCVp m q.toNat = some cv) (hq : q.toNat + 3 < 2 ^ 64) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ m'.arr64 EREC = m.arr64 EREC ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some cv.levelParams ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨-, hl, -⟩ := decCV_some (a := erA m) (q := q.toNat) hcv
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hl
  obtain ⟨o', ho, l', hl', hs⟩ := hl
  have hq2 : (q + 2).toNat = q.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have hr2 : rdW (m.arr64 EREC) (q + 2) = UInt64.ofNat l' := by
    simp only [nat?, erA, Option.map_eq_some_iff] at hl'
    obtain ⟨w, hw, rfl⟩ := hl'
    simp [rdW, hq2, hw]
  rcases Nat.eq_zero_or_pos l' with h0 | hpos
  · subst h0
    have : cv.levelParams = [] := by simpa [hslice?] using hs.symm
    rw [this]
    simp only [cvLpsW, hr2, show (UInt64.ofNat 0 : Word) = 0 from rfl, erToIwW] at h
    obtain ⟨hI1, hE1, hsz, hEs, hc⟩ := hS.2
    rcases hal : allocW m 0 with _ | ⟨q0, m1⟩; · rw [hal] at h; simp at h
    obtain ⟨hS1, hg1, -, -⟩ := allocW_stage hal hS
    obtain ⟨rfl, rfl, -⟩ := allocW_facts hal hsz
    rw [hal] at h
    simp only at h
    generalize n - 1 - 1 = k at h
    cases k with
    | zero => simp [erCopyW] at h
    | succ k =>
    simp only [erCopyW_nil k _ _ _ _ rfl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨hS1, hg1, ?_, by simp [decHL, hslice?], ?_⟩
    · exact (allocMem_frame m 0).1 EREC (by decide) (by decide)
    · have := allocMem_top m 0 hc; simp only [iwTop, this]; simp
  · have hb := L.Ind.hslice?_bound (erA m) l' o' _ hs hpos
    have hq1 : (q + 1).toNat = q.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hr1 : rdW (m.arr64 EREC) (q + 1) = UInt64.ofNat o' := by
      simp only [nat?, erA, Option.map_eq_some_iff] at ho
      obtain ⟨w, hw, rfl⟩ := ho
      simp [rdW, hq1, hw]
    have hEs := hS.2.2.2.2.1
    have hob : o' < 2 ^ 64 := by simp [erA] at hb; omega
    have hlb : l' < 2 ^ 64 := by simp [erA] at hb; omega
    have hlp : (rdW (m.arr64 EREC) (q + 1)).toNat + (rdW (m.arr64 EREC) (q + 2)).toNat ≤ (m.arr64 EREC).size := by
      rw [hr1, hr2, UInt64.toNat_ofNat_of_lt' hob, UInt64.toNat_ofNat_of_lt' hlb]; simpa [erA] using hb
    exact cvLpsW_stage h hS hcv hq (.inr hlp)

/-! ## `nest_holes(_go)` refines `nestHoles(.go)` -/

theorem snocW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m'))
    (hS : StageR dn vis fe m a) : StageR dn vis fe m' a := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, ite_false] at h
  rcases hal : allocW m (l + 1) with _ | ⟨q, m1⟩; · simp [hal] at h
  simp only [hal] at h
  rcases hcp : copyW (n - 1) m1 q o l with _ | m2; · simp [hcp] at h
  simp only [hcp, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨-, rfl⟩ := h
  exact (StageR.ofCopyW _ hcp (hS.alloc hal).1).set_iw _ _

mutual
def nhGoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, ctx, mm, off, l, oo, ol =>
    if l = 0 then some ([1, oo, ol], m)
    else nhK1 k vis ctx mm off l oo ol (envFindW m (rdW (m.arr64 IW) off) vis)
def nhK1 (k : Nat) (vis ctx mm off l oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0, 0, 0], m1)
    else nhK2 k vis ctx mm off l oo ol (instW k m1 (rdW (m1.arr64 IW) (ctx + 7)) (rdW (m1.arr64 IW) (ctx + 8))
      (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4)))
def nhK2 (k : Nat) (vis ctx mm off l oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0, 0, 0], m2)
    else nhK3 k vis ctx mm off l oo ol (fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0))
def nhK3 (k : Nat) (vis ctx mm off l oo ol : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (v, m3) => if 4294967296 ≤ v then none else nhK4 k vis ctx mm off l (snocW k m3 oo ol v)
def nhK4 (k : Nat) (vis ctx mm off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => nhGoW k m4 vis ctx (mm + 1) (off + 1) (l - 1) (r4.headD 0) (r4.tail.headD 0)
end

section arms
variable (k : Nat) (m m1 m2 m3 m4 : Mem) (vis ctx mm off l oo ol v : Word) (r r2 r4 : List Word)
theorem nhGoW_nil (h : l = 0) : nhGoW (k + 1) m vis ctx mm off l oo ol = some ([1, oo, ol], m) := by
  simp [nhGoW, h]
theorem nhGoW_cons (h : ¬ l = 0) : nhGoW (k + 1) m vis ctx mm off l oo ol =
    nhK1 k vis ctx mm off l oo ol (envFindW m (rdW (m.arr64 IW) off) vis) := by simp [nhGoW, h]
theorem nhK1_miss (h : r.headD 0 = 0) : nhK1 k vis ctx mm off l oo ol (some (r, m1)) = some ([0, 0, 0], m1) := by
  rw [nhK1, ite_eq_left h]
theorem nhK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    nhK1 k vis ctx mm off l oo ol (some (r, m1)) = some ([0, 0, 0], m1) := by rw [nhK1, ite_eq_right h, ite_eq_left h3]
theorem nhK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    nhK1 k vis ctx mm off l oo ol (some (r, m1)) =
      nhK2 k vis ctx mm off l oo ol (instW k m1 (rdW (m1.arr64 IW) (ctx + 7)) (rdW (m1.arr64 IW) (ctx + 8))
        (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4))) := by rw [nhK1, ite_eq_right h, ite_eq_right h3]
theorem nhK2_none (h : r2.headD 0 = 0) : nhK2 k vis ctx mm off l oo ol (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [nhK2, ite_eq_left h]
theorem nhK2_some (h : ¬ r2.headD 0 = 0) : nhK2 k vis ctx mm off l oo ol (some (r2, m2)) =
    nhK3 k vis ctx mm off l oo ol (fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0)) := by
  rw [nhK2, ite_eq_right h]
theorem nhK3_big (h : 4294967296 ≤ v) : nhK3 k vis ctx mm off l oo ol (some (v, m3)) = none := by
  rw [nhK3, ite_eq_left h]
theorem nhK3_ok (h : ¬ 4294967296 ≤ v) : nhK3 k vis ctx mm off l oo ol (some (v, m3)) =
    nhK4 k vis ctx mm off l (snocW k m3 oo ol v) := by rw [nhK3, ite_eq_right h]
theorem nhK4_some : nhK4 k vis ctx mm off l (some (r4, m4)) =
    nhGoW k m4 vis ctx (mm + 1) (off + 1) (l - 1) (r4.headD 0) (r4.tail.headD 0) := by rw [nhK4]
end arms
attribute [ind_grind] nhGoW_nil nhGoW_cons nhK1_miss nhK1_noind nhK1_ind nhK2_none nhK2_some nhK3_big
  nhK3_ok nhK4_some

/-- The lookups of `nest_holes`. -/
structure NhLook (p : Prog) : Prop where
  hi1 : I1Prog p
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hsn : p.lookup "sl_snoc" = some slSnoc
  hv : p.lookup "e_view" = some eView
  hip : p.lookup "inst_pis_with" = some instPisWith
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hff : p.lookup "fvar_find" = some fvarFind
  hfp : p.lookup "fvar_push" = some fvarPush
  hif : p.lookup "intern_fvar" = some internFVar
  hgo : p.lookup "nest_holes_go" = some nestHolesGoL
  hp : p.lookup "nest_holes" = some nestHolesL

theorem nhGo_spec (p : Prog) (hl : NhLook p) (k : Nat) :
    ∀ (s₀ : St) (vis ctx mm off l oo ol : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_holes_go" [vis, ctx, mm, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ nhGoW k s₀.mem vis ctx mm off l oo ol =
      some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis ctx mm off l oo ol
    rw [invoke_eq _ hl.hgo]; simp only [callFn, nestHolesGoL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis ctx mm off l oo ol
    simp only [invoke_eq _ hl.hgo, callFn, nestHolesGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p hl.hx hl.hg hl.hf k, instPisWith_spec p hl.hv hl.hip hl.hi1 k,
        internFVar_spec p hl.hff hl.hfp hl.hif k, slSnoc_specW p hl.ha hl.hc hl.hsn k, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The model of `nest_holes(vis, ctx)` at exec fuel `k + 1`. -/
def nhW (k : Nat) (m : Mem) (vis ctx : Word) : Option (List Word × Mem) :=
  nhGoW k m vis ctx 0 (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) 0 0

theorem nestHoles_spec (p : Prog) (hl : NhLook p) (k : Nat) (s₀ : St) (vis ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_holes" [vis, ctx]
    ⦃fun r s' => LocEq s' s₀ ∧
      nhW k s₀.mem vis ctx = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestHolesL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, nhGo_spec p hl k] <;>
    finish (gen := 20) [nhW, rdW_eq]

/-- A `NestCtx` record's slices end below the pool's top (`CtxIn` covers their words, this their
offsets when empty too). -/
def CtxSl (m : Mem) (p : Nat) : Prop :=
  ∀ i, (i = 0 ∨ i = 2 ∨ i = 5 ∨ i = 7) → ∀ o l, iwN m (p + i) = some o → iwN m (p + i + 1) = some l →
    o + l ≤ iwTop m

theorem CtxSl.grow {m m' : Mem} {p : Nat} (h : CtxSl m p) (hin : CtxIn m p (· < iwTop m))
    (hg : IWGrow m m') : CtxSl m' p := by
  intro i hi o l ho hl
  have e0 := iwN_agree (RdS.of_grow hg) (hin.1 i (by omega))
  have e1 := iwN_agree (RdS.of_grow hg) (show p + i + 1 < iwTop m from by
    have := hin.1 (i + 1) (by omega); simpa [Nat.add_assoc] using this)
  rw [e0] at ho; rw [e1] at hl
  exact Nat.le_trans (h i hi o l ho hl) hg.1

/-- The params slice's end, as the words L reads. -/
theorem ctx_params_end {m : Mem} {p : Word} {c : NestCtx} (hc : decCtx m p.toNat = some c)
    (hin : CtxIn m p.toNat (· < iwTop m)) (hsl : CtxSl m p.toNat) (hsz : iwTop m < 2 ^ 64) :
    (rdW (m.arr64 IW) (p + 7)).toNat + (rdW (m.arr64 IW) (p + 8)).toNat ≤ iwTop m := by
  obtain ⟨-, -, -, -, hpa, -⟩ := decCtx_some hc
  obtain ⟨o7, l7, ho7, hl7, -⟩ := decAt_some hpa
  have h11 := hin.1 10 (by omega)
  have r7 : (rdW (m.arr64 IW) (p + 7)).toNat = o7 := rd_iwN (by simpa using ho7) (by simp; omega)
  have r8 : (rdW (m.arr64 IW) (p + 8)).toNat = l7 := rd_iwN (by simpa using hl7) (by simp; omega)
  rw [r7, r8]; exact hsl 7 (by omega) o7 l7 ho7 hl7

/-- `nest_holes`'s results: `(0, …)` or `(1, off, len)`, a handle slice below the top. -/
def NhOut (m : Mem) (r : List Word) : Option (List EIdx) → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 = 1 ∧ decHL m (r.tail.headD 0).toNat (r.tail.tail.headD 0).toNat = some l ∧
      (r.tail.headD 0).toNat + (r.tail.tail.headD 0).toNat ≤ iwTop m

theorem nhGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis ctx : Word) (c : NestCtx) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (mm off l oo ol : Word) (ns : List NIdx) (out : List EIdx) (r : List Word),
    nhGoW k m vis ctx mm off l oo ol = some (r, m') → StageR dn vis fe m a →
    decCtx m ctx.toNat = some c → CtxIn m ctx.toNat (· < iwTop m) → CtxSl m ctx.toNat →
    decHL m off.toNat l.toNat = some ns → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    decHL m oo.toNat ol.toNat = some out → oo.toNat + ol.toNat ≤ iwTop m →
    c.nP + mm.toNat + l.toNat < 2 ^ 64 →
    ∃ x a', (ConRon.Arena.nestHoles.go fe c mm.toNat ns out).run a = .ok (x, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ NhOut m' r x := by
  induction k with
  | zero => intro m m' a mm off l oo ol ns out r h; simp [nhGoW] at h
  | succ k ih =>
    intro m m' a mm off l oo ol ns out r h hS hc hin hsl hns hnb hout hob hmm
    have hsz := hS.2.2.2.1
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hsz
    have hE := hS.1.env
    by_cases hl0 : l = 0
    · rw [nhGoW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : ns = [] := by simpa [decHL, hslice?] using hns.symm
      subst this
      exact ⟨some out, a, by rw [ConRon.Arena.nestHoles.go]; rfl, hS, IWGrow.refl _, rfl, hout, hob⟩
    rw [nhGoW_cons (h := hl0)] at h
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hns2 := hns
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hns2
    obtain ⟨nn, hnn, ns', hns', rfl⟩ := hns2
    obtain ⟨hwH, hwd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.name) (by simpa [iwH, iwA] using hnn)
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hnb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hmm1 : (mm + 1).toNat = mm.toNat + 1 := word_add_toNat (by simp; omega)
    rw [ConRon.Arena.nestHoles.go.eq_2, ← hwd]
    rcases hef : envFindW m (rdW (m.arr64 IW) off) vis with _ | ⟨r1, m1⟩ <;> rw [hef] at h; · simp [nhK1] at h
    have hm1 := envFindW_mem hef
    rw [hm1] at h hef
    by_cases hf0 : r1.headD 0 = 0
    · rw [nhK1_miss (h := hf0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨-, hfind⟩ := envFindW_miss hef hE hwH hf0
      exact ⟨none, a, by rw [hfind]; rfl, hS, IWGrow.refl _, rfl⟩
    obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hwH hf0
    rw [hci] at hfind
    have hciq := decCI_idx hci
    have hszE := erecP_size_le m
    by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
    · rw [nhK1_noind (h := hf0) (h3 := h3)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
      rw [hfind]
      cases ci with
      | indInfo cv caps =>
        exfalso
        have hk := decCI_indInfo_kind hci
        exact h3 (by
          have := erecP_rdN hk rfl
          exact UInt64.toNat_inj.mp (by rw [this]; rfl))
      | _ => rfl
    rw [nhK1_ind (h := hf0) (h3 := h3)] at h
    generalize r1.tail.headD 0 = ciq at h hfind hci h3 hciq
    have hk3 : nat? (erecP m) ciq.toNat = some 3 := by
      have : (erecP m)[ciq.toNat]? = (m.arr64 EREC)[ciq.toNat]? := erecP_getE (by omega)
      simp only [nat?, this]
      have hb : ciq.toNat < (m.arr64 EREC).size := by have := hS.2.2.1; omega
      have : rdW (m.arr64 EREC) ciq = 3 := by simpa using h3
      simp [rdW, hb] at this ⊢; rw [this]; rfl
    obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
    have hb16 := decCI_indInfo_bound hci
    have hcv : decCV (erecP m) (ciq.toNat + 1) = some cv := by
      simp only [decCI, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff] at hci
      obtain ⟨kk, hk, hci⟩ := hci
      rw [hk3] at hk; cases hk
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
      obtain ⟨cv', h1, _, _, h2⟩ := hci
      cases h2; exact h1
    obtain ⟨w, hw, hwH', hwd'⟩ := hd?_some (decCV_type hcv)
    have e4 : (ciq + 4).toNat = ciq.toNat + 1 + 3 := by
      rw [word_add_toNat (by have := hS.2.2.1; have := hS.2.2.2.2.1; simp; omega)]; rfl
    have hrw : rdW (m.arr64 EREC) (ciq + 4) = w := by simp [rdW, e4, erecP_get hw]
    rw [hrw] at h
    simp only [hfind]
    -- the former's type at the parameters
    obtain ⟨hnames, hnamesb, hpa, hpab, hnP, -, -, -, -, h11⟩ := ctx_fields hc hin htop
    have hpe := ctx_params_end hc hin hsl htop
    rcases hinst : instW k m (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8)) w with _ | ⟨r2, m2⟩ <;> rw [hinst] at h; · simp [nhK2] at h
    obtain ⟨x, a2, hrun2, hS2, hg2, hx⟩ := instW_ok k dn fe vis m m2 a _ _ w c.params r2 hinst hS hwH' hpa
      (by omega) hpe
    rw [hwd']
    have hRm2 : RdS m m2 (· < iwTop m) := RdS.of_grow hg2
    cases x with
    | none =>
      have : r2.headD 0 = 0 := hx
      rw [nhK2_none (h := this)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      exact ⟨none, a2, by simp only [StateT.run_bind, hrun2, except_ok_bind]; rfl, hS2, hg2, rfl⟩
    | some t =>
    obtain ⟨hx1, htH, htd⟩ := hx
    rw [nhK2_some (h := by rw [hx1]; decide)] at h
    have hnP2 : (rdW (m2.arr64 IW) (ctx + 4)).toNat = c.nP := by
      have : rdW (m2.arr64 IW) (ctx + 4) = rdW (m.arr64 IW) (ctx + 4) := by
        have e : (ctx + 4).toNat = ctx.toNat + 4 := word_add_toNat (by simp; omega)
        simp only [rdW, e]; rw [hg2.2.2.1 _ (by omega)]
      rw [this, hnP]
    have hu : (rdW (m2.arr64 IW) (ctx + 4) + mm).toNat = c.nP + mm.toNat := by
      rw [word_add_toNat (by rw [hnP2]; omega), hnP2]
    rcases hfv : fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0) with _ | ⟨v, m3⟩ <;> rw [hfv] at h; · simp [nhK3] at h
    obtain ⟨a3, hrun3, hS3, hg3⟩ := internFVar_stage hS2 _ _ htH hfv
    by_cases hvb : 4294967296 ≤ v
    · rw [nhK3_big (h := hvb)] at h; simp at h
    rw [nhK3_ok (h := hvb)] at h
    have hvlt := lt_of_notbig hvb
    have hg23 := hg2.trans hg3
    have hout3 : decHL m3 oo.toNat ol.toNat = some out := by
      rw [decHL_agree (RdS.of_grow hg23) (fun j hj => by omega)]; exact hout
    rcases hsn : snocW k m3 oo ol v with _ | ⟨r4, m4⟩ <;> rw [hsn] at h; · simp [nhK4] at h
    rw [nhK4_some] at h
    obtain ⟨hr4, hdec4, hg4, -, hol1, ht4⟩ := snocW_dec hsn hS3.2.2.2.1 hS3.2.2.2.2.2
      (by have := hg23.1; omega) hvlt hout3
    have hS4 := snocW_stage hsn hS3
    subst hr4
    simp only [List.headD_cons, List.tail_cons] at h
    have hg24 := hg23.trans hg4
    obtain ⟨xr, a', hrun, hS', hg', hout'⟩ := ih m4 m' a3 (mm + 1) (off + 1) (l - 1) _ _ ns' (out ++ [decI v]) r h
      hS4 (by rw [(CtxIn.grow hin hg24).1]; exact hc) (CtxIn.grow hin hg24).2 (hsl.grow hin hg24)
      (by rw [hoff1, hl1, decHL_agree (RdS.of_grow hg24) (fun j hj => by
            have := hnb (j + 1) (by omega); omega)]; simpa [decHL] using hns')
      (fun j hj => by rw [hoff1, hl1] at *; have := hnb (j + 1) (by omega); have := hg24.1; omega)
      hdec4 (by omega) (by rw [hmm1, hl1]; omega)
    refine ⟨xr, a', ?_, hS', hg24.trans hg', hout'⟩
    simp only [StateT.run_bind, hrun2, except_ok_bind]
    simp only [internFVarE]
    rw [← hu, ← htd, ← decE_eq, hrun3]
    simp only [except_ok_bind]
    rw [hmm1] at hrun
    exact hrun

section census
variable (p : Prog) (hl : NhLook p)
include hl

/-- **`nest_holes` refines `nestHoles`** (through `inst_pis_with`'s stub; the ctx's slices end below
the top and `nP + |names| < 2^64`). -/
@[refines ConRon.Arena.nestHoles]
theorem nestHoles_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx : Word) (c : NestCtx) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : decCtx s₀.mem ctx.toNat = some c) (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem))
    (hsl : CtxSl s₀.mem ctx.toNat) (hhi : c.hiAt 0 < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_holes" [vis, ctx]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestHoles fe c) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestHoles fe c) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      NhOut s'.mem r (AM.res (ConRon.Arena.nestHoles fe c) a₀); ⊤⦄ := by
  refine triple_post (nestHoles_spec p hl k s₀ vis ctx) ?_
  rintro r s' ⟨hlc, hm⟩
  have htop : iwTop s₀.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hnb, -⟩ := ctx_fields hc hin htop
  have hlen := decHL_length _ hn
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nhGoW_ok dn fe vis ctx c k _ _ a₀ 0 _ _ 0 0 c.names [] _ hm hS hc hin
    hsl hn hnb (by simp [decHL, hslice?]) (by simp) (by have := hlen; simp [NestCtx.hiAt] at hhi; simp; omega)
  have he : ConRon.Arena.nestHoles fe c = ConRon.Arena.nestHoles.go fe c 0 c.names [] := rfl
  simp only [show (0 : Word).toNat = 0 from rfl, ← he] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hS', hg, ?_⟩
  rw [hres]
  cases x with
  | none => exact hout
  | some l => obtain ⟨h1, h2, h3⟩ := hout; exact ⟨h1, h2, h3⟩

/-- **`nest_holes_go` refines `nestHoles.go`**: from member `mm` on, the names `ns` (a slice of the
context's names below the top) appended to the holes so far (`out`, below the top). Its one caller,
`nestHoles` (`nestHoles_refines` above), discharges every hypothesis from its own pre: the context
decoded with its words and slices below the top, `nP + |names| < 2^64`. -/
@[refines ConRon.Arena.nestHoles.go]
theorem nestHolesGo_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx mm off l oo ol : Word) (c : NestCtx) (ns : List NIdx) (out : List EIdx)
    (hS : StageR dn vis fe s₀.mem a₀) (hc : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hsl : CtxSl s₀.mem ctx.toNat)
    (hns : decHL s₀.mem off.toNat l.toNat = some ns) (hnb : ∀ j < l.toNat, off.toNat + j < iwTop s₀.mem)
    (hout : decHL s₀.mem oo.toNat ol.toNat = some out) (hob : oo.toNat + ol.toNat ≤ iwTop s₀.mem)
    (hmm : c.nP + mm.toNat + l.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_holes_go" [vis, ctx, mm, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestHoles.go fe c mm.toNat ns out) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestHoles.go fe c mm.toNat ns out) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ NhOut s'.mem r (AM.res (ConRon.Arena.nestHoles.go fe c mm.toNat ns out) a₀); ⊤⦄ := by
  refine triple_post (nhGo_spec p hl k s₀ vis ctx mm off l oo ol) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hNh⟩ := nhGoW_ok dn fe vis ctx c k _ _ a₀ mm off l oo ol ns out _ hm hS hc hin
    hsl hns hnb hout hob hmm
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hS', hg, ?_⟩
  rw [hres]
  cases x with
  | none => exact hNh
  | some l => obtain ⟨h1, h2, h3⟩ := hNh; exact ⟨h1, h2, h3⟩

end census

/-! ## `nest_root_canon` refines `nestRootCanon` -/

/-- The lookups of `nest_canon_crest`. -/
structure PccLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hl : AhLook p
  hk : MkLook p
  hng : p.lookup "nest_phs_go" = some nestPhsGo
  hnp : p.lookup "nest_phs" = some nestPhs
  hip : p.lookup "inst_pis_with" = some instPisWith
  hf : p.lookup "ra_find" = some (memoFindG raSch)
  hput : p.lookup "ra_put" = some (memoPutG raSch)
  hgo : p.lookup "replace_apps_go" = some replaceAppsGo
  hnode : p.lookup "replace_apps_node" = some replaceAppsNode
  hcl : p.lookup "ra_clear" = some (memoClearG raSch)
  hra : p.lookup "replace_apps" = some replaceApps
  hp : p.lookup "nest_canon_crest" = some nestCanonCrest
  hp' : p.lookup "nest_root_canon" = some nestRootCanonL

def nrcK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => some ([r3.headD 0, r3.tail.headD 0], m3)
def nrcK2 (k : Nat) (ctx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => nrcK3 (pccW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1))
      (rdW (m2.arr64 IW) (ctx + 10)) (rdW (m2.arr64 IW) (ctx + 4)) (r2.headD 0))
def nrcK1 (cR : CallM) (k : Nat) (ctx cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => nrcK2 k ctx (cR (k + 2) "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0,
      rdW (m1.arr64 IW) (ctx + 10), rdW (m1.arr64 EREC) (cv + 3)] m1)
/-- The model of `nest_root_canon(ctx, cv)` at exec fuel `k + 3` (its `inst_lp_fast` read through `cR`). -/
def nrcW (cR : CallM) (k : Nat) (m : Mem) (ctx cv : Word) : Option (List Word × Mem) :=
  nrcK1 cR k ctx cv (cvLpsW (k + 2) m cv)

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m3 : Mem) (ctx cv : Word) (r1 r2 r3 : List Word)
theorem nrcK3_some : nrcK3 (some (r3, m3)) = some ([r3.headD 0, r3.tail.headD 0], m3) := rfl
theorem nrcK2_some : nrcK2 k ctx (some (r2, m2)) = nrcK3 (pccW k m2 (rdW (m2.arr64 IW) ctx)
    (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 10)) (rdW (m2.arr64 IW) (ctx + 4)) (r2.headD 0)) := rfl
theorem nrcK1_some : nrcK1 cR k ctx cv (some (r1, m1)) = nrcK2 k ctx (cR (k + 2) "inst_lp_fast" [CWF, r1.headD 0,
    r1.tail.headD 0, rdW (m1.arr64 IW) (ctx + 10), rdW (m1.arr64 EREC) (cv + 3)] m1) := rfl
end arms
attribute [ind_grind] nrcK3_some nrcK2_some nrcK1_some

theorem nestRootCanon_spec (p : Prog) (hl : PccLook p) (hc : p.lookup "er_copy" = some erCopy)
    (he : p.lookup "er_to_iw" = some erToIw) (hcv : p.lookup "cv_lps" = some cvLps)
    (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St) (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 3)) "nest_root_canon" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nrcW cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp', callFn, nestRootCanonL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      cvLps_spec p hl.ha hc he hcv (k + 2), hcR (k + 2) "inst_lp_fast",
      nestCanonCrest_spec p hl.ha hl.hl hl.hk hl.hng hl.hnp hl.hip hl.hf hl.hput hl.hgo hl.hnode hl.hcl
        hl.hra hl.hp k] <;>
    finish (gen := 20) [nrcW, rdW_eq]

/-- The names slice's end, as the words L reads. -/
theorem ctx_names_end {m : Mem} {p : Word} {c : NestCtx} (hc : decCtx m p.toNat = some c)
    (hin : CtxIn m p.toNat (· < iwTop m)) (hsl : CtxSl m p.toNat) (hsz : iwTop m < 2 ^ 64) :
    (rdW (m.arr64 IW) p).toNat + (rdW (m.arr64 IW) (p + 1)).toNat ≤ iwTop m := by
  obtain ⟨hn, -⟩ := decCtx_some hc
  obtain ⟨o, l, ho, hl, -⟩ := decAt_some hn
  have h11 := hin.1 10 (by omega)
  have r0 : (rdW (m.arr64 IW) p).toNat = o := by
    have := rd_iwN (m := m) (p := p) (i := 0) (by simpa using ho) (by simp; omega); simpa using this
  have r1 : (rdW (m.arr64 IW) (p + 1)).toNat = l := rd_iwN (by simpa using hl) (by simp; omega)
  rw [r0, r1]; exact hsl 0 (by omega) o l (by simpa using ho) hl

/-- `nest_canon_crest` keeps `AbsOK` (`IndRealAbsPos.pccW_afr`; a hypothesis here, proved below). -/
def PccAfr : Prop :=
  ∀ (k : Nat) (m m' : Mem) (no nl us nn cty : Word) (r : List Word), pccW k m no nl us nn cty = some (r, m') →
    AFr m m'

theorem nrcW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : IlpRd cR dn vis fe (IlpBase m a))
    (h : nrcW cR k m ctx cv = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv)
    (hnn : c.nP + c.names.length < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestRootCanon c cvv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ decOE m' r x ∧ PosMR m' ∧ (PccAfr → AFr m m') := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨-, -, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hcv3 : cv.toNat + 3 < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_le m; omega
  have hEb : erTop m ≤ (m.arr64 EREC).size := hS.2.2.1
  have hEs : (m.arr64 EREC).size < 2 ^ 64 := hS.2.2.2.2.1
  unfold nrcW at h
  rcases hlp : cvLpsW (k + 2) m cv with _ | ⟨r1, m1⟩ <;> rw [hlp] at h; · simp [nrcK1] at h
  rw [nrcK1_some] at h
  obtain ⟨hS1, hg1, hE1, hdec1, -⟩ := pos2_cvLpsW_stage hlp hS ((erecP_ext m).decCV hcv) (by omega)
  -- the instantiation's arguments
  obtain ⟨cin1, cin1'⟩ := CtxIn.grow hin hg1
  rw [hc] at cin1
  have htop1 : iwTop m1 < 2 ^ 64 := Nat.lt_of_le_of_lt hS1.2.1 hS1.2.2.2.1
  obtain ⟨-, -, -, -, -, hlvH, hlvd, -⟩ := ctx_fields cin1 cin1' htop1
  have e3 : (cv + 3).toNat = cv.toNat + 3 := word_add_toNat (by simp; omega)
  have hrd3 : rdW (m1.arr64 EREC) (cv + 3) = wt := by
    rw [hE1]; simp [rdW, e3, erecP_get hwt]
  rw [hrd3] at h
  rcases hst : cR (k + 2) "inst_lp_fast" [CWF, r1.headD 0, r1.tail.headD 0, rdW (m1.arr64 IW) (ctx + 10), wt] m1 with _ | ⟨r2, m2⟩ <;> rw [hst] at h; · simp [nrcK2] at h
  rw [nrcK2_some] at h
  obtain ⟨t, a2, hrun2, ⟨hS2, hg2, htH, htd⟩, ⟨A2, C2, hA2s, hC2s, hfr2⟩, hAF2⟩ :=
    hI (k + 2) CWF _ _ _ _ cvv.levelParams _ _ a r2 hlvH hwtH ⟨rfl, erToIwW_iwFr hlp⟩ hS1 hdec1 hst
  have hP2 : PosMR m2 := (hP.fr (posmemo_cvLpsW_mfr hlp)).fr (MFr.of_frame hfr2 hA2s hC2s)
  obtain ⟨mp2, hM2⟩ := hP2.rp
  rw [CWF_eq, hlvd, ← hwtd] at hrun2
  have hg12 := hg1.trans hg2
  obtain ⟨cin2, cin2'⟩ := CtxIn.grow hin hg12
  rw [hc] at cin2
  have hsl2 := hsl.grow hin hg12
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -, -, -, hnP2, hlvH2, hlvd2, -⟩ := ctx_fields cin2 cin2' htop2
  have hne2 := ctx_names_end cin2 cin2' hsl2 htop2
  rcases hpc : pccW k m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) (rdW (m2.arr64 IW) (ctx + 10))
      (rdW (m2.arr64 IW) (ctx + 4)) (r2.headD 0) with _ | ⟨r3, m3⟩; · rw [hpc] at h; simp [nrcK3] at h
  rw [hpc, nrcK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a3, hrun3, hS3, hg3, hx, hM3⟩ := pccW_ok k dn fe vis m2 m3 a2 _ _ _ _ _ c.names r3 hpc hS2 htH hlvH2 hn2
    (by omega) hne2 (by rw [hnP2]; omega) mp2 hM2
  refine ⟨x, a3, ?_, hS3, hg12.trans hg3, ?_, hP2.setRp (pccW_mfr hpc) hM3,
    fun hpcc => (AFr.iw (erToIwW_iwFr hlp)).trans (hAF2.trans (hpcc _ _ _ _ _ _ _ _ _ hpc))⟩
  · simp only [ConRon.Arena.nestRootCanon, StateT.run_bind, hrun2, except_ok_bind]
    rw [hnP2, hlvd2, htd] at hrun3
    exact hrun3
  · cases x with
    | none => exact hx
    | some e => exact hx

section census
variable (p : Prog) (hl : PccLook p) (hc : p.lookup "er_copy" = some erCopy)
  (he : p.lookup "er_to_iw" = some erToIw) (hcv : p.lookup "cv_lps" = some cvLps)
include hl hc he hcv

end census

/-! ## `nest_uniform_ok` refines `nestUniformOk` -/

def nuK3 : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (o, m3) => some ([if o = 0 then 1 else 0], m3)
def nuK2 (k : Nat) (ctx : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    if r2.headD 0 = 0 then some ([0], m2)
    else nuK3 (noConstWf (k + 3) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) 0 0 (r2.tail.headD 0))
def nuK1 (cR : CallM) (k : Nat) (ctx cv : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => if r1.headD 0 ≠ 0 then some ([0], m1) else nuK2 k ctx (nrcW cR k m1 ctx cv)
/-- The model of `nest_uniform_ok(ctx, cv)` at exec fuel `k + 4`. -/
def nuW (cR : CallM) (k : Nat) (m : Mem) (ctx cv : Word) : Option (List Word × Mem) :=
  nuK1 cR k ctx cv (pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
    (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)))

section arms
variable (cR : CallM) (k : Nat) (m1 m2 m3 : Mem) (ctx cv o : Word) (r1 r2 : List Word)
theorem nuK3_some : nuK3 (some (o, m3)) = some ([if o = 0 then 1 else 0], m3) := rfl
theorem nuK2_none (h : r2.headD 0 = 0) : nuK2 k ctx (some (r2, m2)) = some ([0], m2) := by rw [nuK2, ite_eq_left h]
theorem nuK2_some (h : ¬ r2.headD 0 = 0) : nuK2 k ctx (some (r2, m2)) =
    nuK3 (noConstWf (k + 3) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) 0 0 (r2.tail.headD 0)) := by
  rw [nuK2, ite_eq_right h]
theorem nuK1_occ (h : r1.headD 0 ≠ 0) : nuK1 cR k ctx cv (some (r1, m1)) = some ([0], m1) := by rw [nuK1, ite_eq_left h]
theorem nuK1_ok (h : ¬ r1.headD 0 ≠ 0) : nuK1 cR k ctx cv (some (r1, m1)) = nuK2 k ctx (nrcW cR k m1 ctx cv) := by
  rw [nuK1, ite_eq_right h]
end arms
attribute [ind_grind] nuK3_some nuK2_none nuK2_some nuK1_occ nuK1_ok

/-- The lookups of `nest_uniform_ok`. -/
structure NuLook (p : Prog) : Prop where
  pcc : PccLook p
  no : NoLook p
  hc : p.lookup "er_copy" = some erCopy
  he : p.lookup "er_to_iw" = some erToIw
  hcv : p.lookup "cv_lps" = some cvLps
  hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  hpd : p.lookup "pi_doms_occ" = some piDomsOccL
  hp : p.lookup "nest_uniform_ok" = some nestUniformOkL

theorem nestUniformOk_spec (p : Prog) (hl : NuLook p) (cR : CallM) (hcR : CallSpec p cR) (k : Nat) (s₀ : St)
    (ctx cv : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 4)) "nest_uniform_ok" [ctx, cv]
    ⦃fun r s' => LocEq s' s₀ ∧ nuW cR k s₀.mem ctx cv = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestUniformOkL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      nestCtxHiAt_specE p hl.hh (k + 3), piDomsOcc_spec p hl.no hl.hpd (k + 3),
      nestRootCanon_spec p hl.pcc hl.hc hl.he hl.hcv cR hcR k, nestOcc_spec' p hl.no (k + 3)] <;>
    finish (gen := 20) [nuW, rdW_eq]

/-- What `AbsOK` across `nest_uniform_ok` needs of its callees (`IndRealAbsPos.nuAfr`). -/
structure NuAfr : Prop where
  pcc : PccAfr
  pdo : ∀ (k : Nat) (m m' : Mem) (no nl lo hi n e : Word) (r : List Word), pdoW k m no nl lo hi n e = some (r, m') →
    AFr m m'
  noc : ∀ (k : Nat) (m m' : Mem) (no nl lo hi e o : Word), noConstWf k m no nl lo hi e = some (o, m') → AFr m m'

theorem nuW_ok (k : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (m m' : Mem)
    (a : AState) (ctx cv : Word) (c : NestCtx) (cvv : IConstantVal) (r : List Word) (cR : CallM)
    (hI : ∀ (m1 : Mem) (a1 : AState) (r1 : List Word) (b : Bool),
      pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
        (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) (rdW (m.arr64 EREC) (cv + 3)) = some (r1, m1) →
      (ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type).run a = .ok (b, a1) →
      StageR dn vis fe m1 a1 → IlpRd cR dn vis fe (IlpBase m1 a1))
    (h : nuW cR k m ctx cv = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsl : CtxSl m ctx.toNat)
    (hcv : decCV (erecP m) cv.toNat = some cvv) (hhi : c.hiAt 0 < 2 ^ 64) (hP : PosMR m) :
    ∃ x a', (ConRon.Arena.nestUniformOk c cvv).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ r = [if x then 1 else 0] ∧ PosMR m' ∧ (NuAfr → AFr m m') := by
  have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hn, hnb, -, -, hnP, -⟩ := ctx_fields hc hin htop
  have hhiW := nhiW_toNat (nf := 0) hc hin htop (by simpa using hhi)
  obtain ⟨-, -, hty⟩ := decCV_some hcv
  obtain ⟨wt, hwt, hwtH, hwtd⟩ := hd?_some hty
  have hcv3 : cv.toNat + 3 < erTop m := by
    have := (Array.getElem?_eq_some_iff.mp hwt).1; have := erecP_size_le m; omega
  have e3 : (cv + 3).toNat = cv.toNat + 3 := word_add_toNat (by have := hS.2.2.1; have := hS.2.2.2.2.1; simp; omega)
  have hrd3 : rdW (m.arr64 EREC) (cv + 3) = wt := by simp [rdW, e3, erecP_get hwt]
  unfold nuW at h
  rw [hrd3] at h
  obtain ⟨mp0, hM0⟩ := hP.no
  rcases hpd : pdoW (k + 3) m (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) (rdW (m.arr64 IW) (ctx + 4))
      (nhiW m ctx 0) (rdW (m.arr64 IW) (ctx + 4)) wt with _ | ⟨r1, m1⟩; · rw [hpd] at h; simp [nuK1] at h
  rw [hpd] at h
  obtain ⟨b1, a1, mp1, hrun1, hS1, hg1, hr1, hM1, hf1⟩ := pdoW_ok dn fe vis _ _ _ _ c.names (k + 3) m m1 a _ wt r1 mp0
    hpd hS hwtH hn hnb hM0
  have hP1 := hP.setNo hf1 ⟨mp1, hM1⟩
  rw [hnP, hhiW, decE_eq, ← hwtd, show (0 : Word).toNat = 0 from rfl] at hrun1
  have hI1 := hI m1 a1 r1 b1 (by rw [hrd3]; exact hpd) hrun1 hS1
  have hpre : ConRon.Arena.nestUniformOk c cvv = (do
      let o1 ← ConRon.Arena.piDomsOcc c.names c.nP (c.hiAt 0) c.nP cvv.type
      if o1 = true then pure false
      else match ← ConRon.Arena.nestRootCanon c cvv with
        | none => pure false
        | some crest => do
          let occ ← ConRon.Arena.nestOcc c.names 0 0 crest
          pure !occ) := rfl
  rw [hpre]
  cases b1 with
  | true =>
    rw [nuK1_occ (h := by rw [hr1]; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a1, ?_, hS1, hg1, rfl, hP1, fun hN => hN.pdo _ _ _ _ _ _ _ _ _ _ hpd⟩
    simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
  | false =>
  rw [nuK1_ok (h := by rw [hr1]; decide)] at h
  have hcv1 : decCV (erecP m1) cv.toNat = some cvv := (GrowX.of_grow (q := 0) (n := 0) hg1).erecP.decCV hcv
  rcases hrc : nrcW cR k m1 ctx cv with _ | ⟨r2, m2⟩ <;> rw [hrc] at h; · simp [nuK2] at h
  obtain ⟨cin1, cin1'⟩ := CtxIn.grow hin hg1
  rw [hc] at cin1
  have hnn : c.nP + c.names.length < 2 ^ 64 := by simpa [NestCtx.hiAt] using hhi
  obtain ⟨x2, a2, hrun2, hS2, hg2, hx2, hP2, hA2⟩ := nrcW_ok k dn fe vis m1 m2 a1 ctx cv c cvv r2 cR hI1 hrc hS1 cin1 cin1'
    (hsl.grow hin hg1) hcv1 hnn hP1
  cases x2 with
  | none =>
    rw [nuK2_none (h := hx2)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨false, a2, ?_, hS2, hg1.trans hg2, rfl, hP2,
      fun hN => (hN.pdo _ _ _ _ _ _ _ _ _ _ hpd).trans (hA2 hN.pcc)⟩
    simp only [StateT.run_bind, hrun1, except_ok_bind]
    simp only [Bool.false_eq_true, ite_false, StateT.run_bind, hrun2, except_ok_bind]; rfl
  | some crest =>
  obtain ⟨hx0, hcH, hcd⟩ := hx2
  rw [nuK2_some (h := by rw [hx0]; decide)] at h
  have hg12 := hg1.trans hg2
  obtain ⟨cin2, cin2'⟩ := CtxIn.grow hin hg12
  rw [hc] at cin2
  have htop2 : iwTop m2 < 2 ^ 64 := Nat.lt_of_le_of_lt hS2.2.1 hS2.2.2.2.1
  obtain ⟨hn2, -⟩ := ctx_fields cin2 cin2' htop2
  have hne2 := ctx_names_end cin2 cin2' (hsl.grow hin hg12) htop2
  obtain ⟨mp2, hM2⟩ := hP2.no
  rcases hno : noConstWf (k + 3) m2 (rdW (m2.arr64 IW) ctx) (rdW (m2.arr64 IW) (ctx + 1)) 0 0 (r2.tail.headD 0) with _ | ⟨o, m3⟩ <;> rw [hno] at h; · simp [nuK3] at h
  rw [nuK3_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨b, hrun3, hb, hM3, hS3, hg3, hf3⟩ := noConstWf_ok (k + 3) dn fe vis m2 m3 a2 _ _ 0 0 _ o c.names mp2 hno hS2
    hcH hn2 (by omega) hM2
  refine ⟨!b, a2, ?_, hS3, hg12.trans hg3, ?_, hP2.setNo hf3 ⟨∅, hM3⟩,
    fun hN => ((hN.pdo _ _ _ _ _ _ _ _ _ _ hpd).trans (hA2 hN.pcc)).trans (hN.noc _ _ _ _ _ _ _ _ _ hno)⟩
  · simp only [StateT.run_bind, hrun1, except_ok_bind]
    simp only [Bool.false_eq_true, ite_false, StateT.run_bind, hrun2, except_ok_bind]
    rw [decE_eq, hcd, show (0 : Word).toNat = 0 from rfl] at hrun3
    simp only [hrun3, except_ok_bind]; rfl
  · subst hb; by_cases ho : o = 0 <;> simp [ho]

section census
variable (p : Prog) (hl : NuLook p)
include hl

end census

end L.Ind
