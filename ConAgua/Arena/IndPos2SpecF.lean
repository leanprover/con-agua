import ConAgua.Arena.IndPos2SpecE
import ConAgua.Arena.RecCheckSpec

/-! # `IndPos2`'s leaves, continued (lane `indproofs2`, helper `pos`, fork E): `nestHoles`,
`nestRootCanon`, … -/

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `nest_holes(_go)` refines `nestHoles(.go)` -/

theorem snocW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {n : Nat} {m m' : Mem} {o l x : Word} {r : List Word} (h : snocW n m o l x = some (r, m'))
    (hS : StageR dn vis fe m a) : StageR dn vis fe m' a := by
  simp only [snocW] at h
  by_cases h0 : l + 1 = 0
  · simp [h0] at h
  simp only [h0, if_false] at h
  cases hal : allocW m (l + 1) with
  | none => simp [hal] at h
  | some qm =>
  obtain ⟨q, m1⟩ := qm
  simp only [hal] at h
  cases hcp : copyW (n - 1) m1 q o l with
  | none => simp [hcp] at h
  | some m2 =>
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
  rw [nhK1, if_pos h]
theorem nhK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    nhK1 k vis ctx mm off l oo ol (some (r, m1)) = some ([0, 0, 0], m1) := by rw [nhK1, if_neg h, if_pos h3]
theorem nhK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    nhK1 k vis ctx mm off l oo ol (some (r, m1)) =
      nhK2 k vis ctx mm off l oo ol (instW k m1 (rdW (m1.arr64 IW) (ctx + 7)) (rdW (m1.arr64 IW) (ctx + 8))
        (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4))) := by rw [nhK1, if_neg h, if_neg h3]
theorem nhK2_none (h : r2.headD 0 = 0) : nhK2 k vis ctx mm off l oo ol (some (r2, m2)) = some ([0, 0, 0], m2) := by
  rw [nhK2, if_pos h]
theorem nhK2_some (h : ¬ r2.headD 0 = 0) : nhK2 k vis ctx mm off l oo ol (some (r2, m2)) =
    nhK3 k vis ctx mm off l oo ol (fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0)) := by
  rw [nhK2, if_neg h]
theorem nhK3_big (h : 4294967296 ≤ v) : nhK3 k vis ctx mm off l oo ol (some (v, m3)) = none := by
  rw [nhK3, if_pos h]
theorem nhK3_ok (h : ¬ 4294967296 ≤ v) : nhK3 k vis ctx mm off l oo ol (some (v, m3)) =
    nhK4 k vis ctx mm off l (snocW k m3 oo ol v) := by rw [nhK3, if_neg h]
theorem nhK4_some : nhK4 k vis ctx mm off l (some (r4, m4)) =
    nhGoW k m4 vis ctx (mm + 1) (off + 1) (l - 1) (r4.headD 0) (r4.tail.headD 0) := by rw [nhK4]
end arms
attribute [ind_grind] nhGoW_nil nhGoW_cons nhK1_miss nhK1_noind nhK1_ind nhK2_none nhK2_some nhK3_big
  nhK3_ok nhK4_some

/-- The lookups of `nest_holes`. -/
structure NhLook (p : Prog) : Prop where
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
    rw [invoke_eq _ hl.hgo]
    simp only [callFn, nestHolesGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        envFind_specW p hl.hx hl.hg hl.hf k, instPisWith_spec p hl.hv hl.hip k,
        internFVar_spec p hl.hff hl.hfp hl.hif k, slSnoc_specW p hl.ha hl.hc hl.hsn k, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The model of `nest_holes(vis, ctx)` at exec fuel `k + 1`. -/
def nhW (k : Nat) (m : Mem) (vis ctx : Word) : Option (List Word × Mem) :=
  nhGoW k m vis ctx 0 (rdW (m.arr64 IW) ctx) (rdW (m.arr64 IW) (ctx + 1)) 0 0

theorem nestHoles_spec (p : Prog) (hl : NhLook p) (k : Nat) (s₀ : St) (vis ctx : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (k + 1)) "nest_holes" [vis, ctx]
    ⦃fun r s' => LocEq s' s₀ ∧
      nhW k s₀.mem vis ctx = some ([r.headD 0, r.tail.headD 0, r.tail.tail.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hl.hp]
  simp only [callFn, nestHolesL]
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
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hl0
      have : ns = [] := by simpa [decHL, hslice?] using hns.symm
      subst this
      exact ⟨some out, a, by rw [ConRon.Arena.nestHoles.go]; rfl, hS, IWGrow.refl _, rfl, hout, hob⟩
    rw [nhGoW_cons (h := hl0)] at h
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hns2 := hns
    simp only [decHL] at hns2
    rw [hl', hslice?_succ] at hns2
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hns2
    obtain ⟨nn, hnn, ns', hns', rfl⟩ := hns2
    obtain ⟨hwH, hwd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.name) (by simpa [iwH, iwA] using hnn)
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hnb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hmm1 : (mm + 1).toNat = mm.toNat + 1 := word_add_toNat (by simp; omega)
    rw [ConRon.Arena.nestHoles.go.eq_2, ← hwd]
    cases hef : envFindW m (rdW (m.arr64 IW) off) vis with
    | none => rw [hef] at h; simp [nhK1] at h
    | some pr =>
    obtain ⟨r1, m1⟩ := pr
    rw [hef] at h
    have hm1 := envFindW_mem hef
    rw [hm1] at h hef
    by_cases hf0 : r1.headD 0 = 0
    · rw [nhK1_miss (h := hf0)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨-, hfind⟩ := envFindW_miss hef hE hwH hf0
      exact ⟨none, a, by rw [hfind]; rfl, hS, IWGrow.refl _, rfl⟩
    obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hwH hf0
    rw [hci] at hfind
    have hciq := decCI_idx hci
    have hszE := erecP_size_le m
    by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
    · rw [nhK1_noind (h := hf0) (h3 := h3)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
    cases hinst : instW k m (rdW (m.arr64 IW) (ctx + 7)) (rdW (m.arr64 IW) (ctx + 8)) w with
    | none => rw [hinst] at h; simp [nhK2] at h
    | some pr2 =>
    obtain ⟨r2, m2⟩ := pr2
    rw [hinst] at h
    obtain ⟨x, a2, hrun2, hS2, hg2, hx⟩ := instW_ok k dn fe vis m m2 a _ _ w c.params r2 hinst hS hwH' hpa
      (by omega) hpe
    rw [hwd']
    have hRm2 : RdS m m2 (· < iwTop m) := RdS.of_grow hg2
    cases x with
    | none =>
      have : r2.headD 0 = 0 := hx
      rw [nhK2_none (h := this)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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
    cases hfv : fvinternW m2 (rdW (m2.arr64 IW) (ctx + 4) + mm) (r2.tail.headD 0) with
    | none => rw [hfv] at h; simp [nhK3] at h
    | some pr3 =>
    obtain ⟨v, m3⟩ := pr3
    rw [hfv] at h
    obtain ⟨a3, hrun3, hS3, hg3⟩ := internFVar_stage hS2 _ _ htH hfv
    by_cases hvb : 4294967296 ≤ v
    · rw [nhK3_big (h := hvb)] at h; simp at h
    rw [nhK3_ok (h := hvb)] at h
    have hvlt := lt_of_notbig hvb
    have hg23 := hg2.trans hg3
    have hout3 : decHL m3 oo.toNat ol.toNat = some out := by
      rw [decHL_agree (RdS.of_grow hg23) (fun j hj => by omega)]; exact hout
    cases hsn : snocW k m3 oo ol v with
    | none => rw [hsn] at h; simp [nhK4] at h
    | some pr4 =>
    obtain ⟨r4, m4⟩ := pr4
    rw [hsn, nhK4_some] at h
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
    simp only [internFVarE, StateT.run_bind]
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
  rw [show (0 : Word).toNat = 0 from rfl] at hrun
  rw [← he] at hrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hS', hg, ?_⟩
  rw [hres]
  cases x with
  | none => exact hout
  | some l => obtain ⟨h1, h2, h3⟩ := hout; exact ⟨h1, h2, h3⟩

end census

end L.Ind
