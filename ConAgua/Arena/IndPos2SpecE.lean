import ConAgua.Arena.IndPosSpec2
import ConAgua.Arena.IndRealWalk
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndDecStab

/-! # `IndPos2`'s leaves (lane `indproofs2`, helper `pos`, fork E)

`nestArity`, … — the template of `IndPosSpec2.lean`. -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## `pi_binders` under the stage relation -/

/-- **`pi_binders` keeps the stage relation** (it only conses into the pool). -/
theorem piBW_stage {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (fuel h : Word) (rs : List Word),
    piBW n m fuel h = some (rs, m') → StageR dn vis fe m a → H h → StageR dn vis fe m' a := by
  induction n with
  | zero => intro m m' a fuel h rs hh; simp [piBW] at hh
  | succ n ih =>
    intro m m' a fuel h rs hpb hS hh
    have hR := hS.1.arena.1
    by_cases hf : fuel = 0
    · rw [piBW_fuel0 n m fuel h hf] at hpb; simp at hpb
    by_cases hg : h >>> 28 ≠ 6
    · rw [piBW_leaf n m fuel h hf hg] at hpb
      simp only [Option.some.injEq, Prod.mk.injEq] at hpb
      obtain ⟨-, rfl⟩ := hpb; exact hS
    rw [piBW_node n m fuel h hf hg] at hpb
    have hg6 : h >>> 28 = 6 := by simpa using hg
    by_cases hr : eViewW m h = []
    · rw [hr, piBK1_nil] at hpb; simp at hpb
    obtain ⟨hvok, hew⟩ := eViewW_forall m h hg6 hr
    rw [piBK1_ne n m fuel _ hr] at hpb
    rcases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with _ | ⟨rs1, m1⟩ <;> rw [hrec] at hpb; · simp [piBK2] at hpb
    rw [piBK2_some] at hpb
    rcases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs1.headD 0) (rs1.getD 1 0) with _ | ⟨r2, m2⟩ <;> rw [hcons] at hpb; · simp [piBK3] at hpb
    rw [piBK3_some] at hpb
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hpb)
    obtain ⟨-, hty, hb⟩ := view_forall m a hR h hh hvok hg6
    have hty2 : ((eViewW m h).getD 1 0).toNat < 2 ^ 32 := by rw [hew]; exact hty
    have hb2 : ((eViewW m h).getD 2 0).toNat < 2 ^ 32 := by rw [hew]; exact hb
    have hS1 := ih m m1 a (fuel - 1) _ rs1 hrec hS hb2
    obtain ⟨bs1, e1, -, -, hdec1, -, -, -, -, hle1⟩ :=
      piBW_ok n m m1 a (fuel - 1) _ rs1 hR hrec hb2 hS.2.2.2.1 hS.2.2.2.2.2
    exact (consW_stage hcons hS1 hle1 hty2 hdec1).1

/-- `pi_binders` at `CWF` from the stage relation: the twin's run, the stage relation kept. -/
theorem piBW_cwf {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {n : Nat} {m m' : Mem}
    {a : AState} {h : Word} {rs : List Word} (hpb : piBW n m CWF h = some (rs, m'))
    (hS : StageR dn vis fe m a) (hh : H h) :
    ∃ bs e, (ConRon.Arena.piBinders coreWalkFuel (decI h)).run a = .ok ((bs, e), a) ∧
      decHL m' (rs.headD 0).toNat (rs.getD 1 0).toNat = some bs ∧
      (rs.getD 2 0).toNat < 2 ^ 32 ∧ decE (rs.getD 2 0) = e ∧
      StageR dn vis fe m' a ∧ IWGrow m m' ∧ (rs.headD 0).toNat + (rs.getD 1 0).toNat ≤ iwTop m' := by
  obtain ⟨bs, e, hrun, -, hdec, hb1, hb2, hg, -, hle⟩ :=
    piBW_ok n m m' a CWF h rs hS.1.arena.1 hpb hh hS.2.2.2.1 hS.2.2.2.2.2
  rw [CWF_eq] at hrun
  exact ⟨bs, e, hrun, hdec, hb1, hb2, piBW_stage n m m' a CWF h rs hpb hS hh, hg, hle⟩

/-! ## `nest_arity` refines `nestArity` -/

def naK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rs, m2) => some ([rs.getD 1 0], m2)
def naK1 (n : Nat) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0], m1)
    else if rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3 then some ([0], m1)
    else naK2 (piBW n m1 CWF (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4)))
/-- The model of `nest_arity(vis, c)` at exec fuel `n + 1`. -/
def naW (n : Nat) (m : Mem) (vis c : Word) : Option (List Word × Mem) := naK1 n (envFindW m c vis)

section arms
variable (n : Nat) (m1 m2 : Mem) (r rs : List Word)
theorem naK2_some : naK2 (some (rs, m2)) = some ([rs.getD 1 0], m2) := rfl
theorem naK1_miss (h : r.headD 0 = 0) : naK1 n (some (r, m1)) = some ([0], m1) := by rw [naK1, ite_eq_left h]
theorem naK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    naK1 n (some (r, m1)) = some ([0], m1) := by rw [naK1, ite_eq_right h, ite_eq_left h3]
theorem naK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    naK1 n (some (r, m1)) = naK2 (piBW n m1 CWF (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4))) := by
  rw [naK1, ite_eq_right h, ite_eq_right h3]
end arms
attribute [ind_grind] naK2_some naK1_miss naK1_noind naK1_ind

/-- The lookups of `nest_arity`. -/
structure NaLook (p : Prog) : Prop where
  ha : p.lookup "iw_alloc" = some iwAlloc
  hc : p.lookup "iw_copy" = some iwCopy
  hv : p.lookup "e_view" = some eView
  hs : p.lookup "sl_cons" = some slCons
  hpb : p.lookup "pi_binders" = some piBinders
  hx : p.lookup "env_ix" = some envIxL
  hg : p.lookup "env_row_get" = some envRowGetL
  hf : p.lookup "env_find" = some envFindL
  hp : p.lookup "nest_arity" = some nestArityL

theorem nestArity_spec (p : Prog) (hl : NaLook p) (n : Nat) (s₀ : St) (vis c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_arity" [vis, c]
    ⦃fun r s' => LocEq s' s₀ ∧ naW n s₀.mem vis c = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hl.hp, callFn, nestArityL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      envFind_specW p hl.hx hl.hg hl.hf n,
      piBinders_spec p hl.ha hl.hc hl.hv hl.hs hl.hpb n] <;>
    finish (gen := 20) [naW, rdW_eq, List.getD_cons_zero, List.getD_cons_succ]

theorem nestArity_none {fe : IFEnv} {C : NIdx} (h : ∀ cv caps, fe.find? C ≠ some (.indInfo cv caps)) :
    ConRon.Arena.nestArity fe C = pure 0 := by
  simp only [ConRon.Arena.nestArity]

theorem naW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis C : Word) (hC : H C)
    (n : Nat) (m m' : Mem) (a : AState) (r : List Word)
    (h : naW n m vis C = some (r, m')) (hS : StageR dn vis fe m a) :
    ∃ x a', (ConRon.Arena.nestArity fe (decI C)).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ (r.headD 0).toNat = x := by
  have hE := hS.1.env
  unfold naW at h
  rcases hef : envFindW m C vis with _ | ⟨r1, m1⟩ <;> rw [hef] at h; · simp [naK1] at h
  have hm1 := envFindW_mem hef
  rw [hm1] at h hef
  by_cases hf0 : r1.headD 0 = 0
  · rw [naK1_miss (h := hf0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨-, hfind⟩ := envFindW_miss hef hE hC hf0
    refine ⟨0, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestArity_none (fun cv caps e => by rw [hfind] at e; cases e)]; rfl
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hC hf0
  rw [hci] at hfind
  have hciq := decCI_idx hci
  have hsz := erecP_size_le m
  by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [naK1_noind (h := hf0) (h3 := h3)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨0, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestArity_none (fun cv caps e => by
      rw [hfind] at e; cases e
      have hk := decCI_indInfo_kind hci
      exact h3 (by
        have := erecP_rdN hk rfl
        exact UInt64.toNat_inj.mp (by rw [this]; rfl)))]; rfl
  rw [naK1_ind (h := hf0) (h3 := h3)] at h
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
    obtain ⟨k, hk, hci⟩ := hci
    rw [hk3] at hk; cases hk
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at hci
    obtain ⟨cv', h1, _, _, h2⟩ := hci
    cases h2; exact h1
  obtain ⟨w, hw, hwH, hwd⟩ := hd?_some (decCV_type hcv)
  have e4 : (ciq + 4).toNat = ciq.toNat + 1 + 3 := by
    rw [word_add_toNat (by have := hS.2.2.1; have := hS.2.2.2.2.1; simp; omega)]; rfl
  have hrw : rdW (m.arr64 EREC) (ciq + 4) = w := by simp [rdW, e4, erecP_get hw]
  rw [hrw] at h
  rcases hpb : piBW n m CWF w with _ | ⟨rs, m2⟩ <;> rw [hpb] at h; · simp [naK2] at h
  rw [naK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨bs, e, hrun, hdec, -, -, hS2, hg2, -⟩ := piBW_cwf hpb hS hwH
  refine ⟨bs.length, a, ?_, hS2, hg2, ?_⟩
  · simp only [ConRon.Arena.nestArity, hfind, StateT.run_bind]
    rw [hwd, hrun]; rfl
  · simp [decHL_length _ hdec]

section census
variable (p : Prog) (hl : NaLook p)
include hl

/-- **`nest_arity` refines `nestArity`**. -/
@[refines ConRon.Arena.nestArity]
theorem nestArity_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis C : Word) (hC : H C) (hS : StageR dn vis fe s₀.mem a₀) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_arity" [vis, C]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestArity fe (decI C)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestArity fe (decI C)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ (r.headD 0).toNat = AM.res (ConRon.Arena.nestArity fe (decI C)) a₀; ⊤⦄ := by
  refine triple_post (nestArity_spec p hl n s₀ vis C) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := naW_ok dn fe vis C hC n _ _ a₀ r hm hS
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `nest_ctx_hi_at` as a word model -/

/-- The model of `nest_ctx_hi_at(ctx, nf)`. -/
def nhiW (m : Mem) (ctx nf : Word) : Word := rdW (m.arr64 IW) (ctx + 4) + rdW (m.arr64 IW) (ctx + 1) + nf

theorem nestCtxHiAt_specE (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt) (n : Nat)
    (s₀ : St) (ctx nf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [ctx, nf]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = nhiW s₀.mem ctx nf; ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestCtxHiAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [nhiW, rdW_eq]

theorem nhiW_toNat {m : Mem} {ctx nf : Word} {c : NestCtx} (hc : decCtx m ctx.toNat = some c)
    (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsz : iwTop m < 2 ^ 64)
    (hhi : c.hiAt nf.toNat < 2 ^ 64) : (nhiW m ctx nf).toNat = c.hiAt nf.toNat := by
  obtain ⟨hn, -, -, -, hnP, -⟩ := ctx_fields hc hin hsz
  have hl := decHL_length m hn
  simp only [NestCtx.hiAt] at hhi ⊢
  simp only [nhiW, UInt64.toNat_add, hnP, hl]
  omega

/-- A decoded handle at `o`, as the word L reads there. -/
theorem rd_iwH0E {k : IdxKind} {m : Mem} {o : Word} {x : Idx k} (h : iwH m o.toNat = some x) :
    H (rdW (m.arr64 IW) o) ∧ decI (rdW (m.arr64 IW) o) = x := by
  obtain ⟨w, hw, hl, hx⟩ := hd?_some h
  simp only [iwA] at hw
  simp only [rdW, hw, Option.getD_some]
  exact ⟨hl, hx.symm⟩

/-! ## `nest_ds_closed(_go)`: `ds.allM (fvarB · ≤ hi)` -/

/-- The twin's per-parameter test. -/
def dsF (hi : Nat) (x : EIdx) : AM Bool := do
  let b ← fvarB coreWalkFuel x
  pure (decide (b ≤ hi))

mutual
def dcGoW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, hi, off, l =>
    if l = 0 then some ([1], m)
    else dcK n hi off l (fvbF m [CWF, rdW (m.arr64 IW) off])
def dcK (n : Nat) (hi off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if hi < r.headD 0 then some ([0], m1) else dcGoW n m1 hi (off + 1) (l - 1)
end

section arms
variable (n : Nat) (m m1 : Mem) (hi off l : Word) (r : List Word)
theorem dcGoW_nil (h : l = 0) : dcGoW (n + 1) m hi off l = some ([1], m) := by simp [dcGoW, h]
theorem dcGoW_cons (h : ¬ l = 0) : dcGoW (n + 1) m hi off l =
    dcK n hi off l (fvbF m [CWF, rdW (m.arr64 IW) off]) := by simp [dcGoW, h]
theorem dcK_out (h : hi < r.headD 0) : dcK n hi off l (some (r, m1)) = some ([0], m1) := by
  rw [dcK, ite_eq_left h]
theorem dcK_in (h : ¬ hi < r.headD 0) : dcK n hi off l (some (r, m1)) = dcGoW n m1 hi (off + 1) (l - 1) := by
  rw [dcK, ite_eq_right h]
end arms
attribute [ind_grind] dcGoW_nil dcGoW_cons dcK_out dcK_in

theorem dcGo_spec (p : Prog) (hf : HfF p) (hp : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL) (n : Nat) :
    ∀ (s₀ : St) (hi off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ds_closed_go" [hi, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ dcGoW n s₀.mem hi off l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi off l
    rw [invoke_eq _ hp]; simp only [callFn, nestDsClosedGoL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi off l
    simp only [invoke_eq _ hp, callFn, nestDsClosedGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        fvbF_spec p hf n, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The model of `nest_ds_closed(ctx, off, l)` at exec fuel `n + 1`. -/
def dcW (n : Nat) (m : Mem) (ctx off l : Word) : Option (List Word × Mem) := dcGoW n m (nhiW m ctx 0) off l

theorem dc_spec (p : Prog) (hf : HfF p) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hg : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL)
    (hp : p.lookup "nest_ds_closed" = some nestDsClosedL) (n : Nat) (s₀ : St) (ctx off l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ds_closed" [ctx, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ dcW n s₀.mem ctx off l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestDsClosedL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      nestCtxHiAt_specE p hh n, dcGo_spec p hf hg n] <;>
    finish (gen := 20) [dcW]

theorem dcGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis hi : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (ds : List EIdx) (r : List Word),
    dcGoW n m hi off l = some (r, m') → StageR dn vis fe m a →
    decHL m off.toNat l.toNat = some ds → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ∃ b a', (ds.allM (dsF HI)).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      r.headD 0 = (if b then 1 else 0) := by
  induction n with
  | zero => intro m m' a off l ds r h; simp [dcGoW] at h
  | succ n ih =>
    intro m m' a off l ds r h hS hds hin
    by_cases hl0 : l = 0
    · rw [dcGoW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : ds = [] := by simpa [decHL, hslice?] using hds.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl⟩
    rw [dcGoW_cons (h := hl0)] at h
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hds' := hds
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hds'
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hds'
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hsz := hS.2.2.2.1
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hin 0 (by omega); have := hS.2.1; omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rcases hst : fvbF m [CWF, rdW (m.arr64 IW) off] with _ | ⟨r1, m1⟩ <;> rw [hst] at h; · simp [dcK] at h
    obtain ⟨k, a1, hrun1, hS1, hg1, hk⟩ := fvbF_ok dn vis fe CWF _ hxH _ _ a r1 hst hS
    rw [CWF_eq, hxd] at hrun1
    rw [List.allM_cons]
    by_cases hc : hi < r1.headD 0
    · rw [dcK_out (h := hc)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hgt : ¬ k ≤ HI := by
        have := UInt64.lt_iff_toNat_lt.mp hc; simp only [decW0Nat] at hk; omega
      refine ⟨false, a1, ?_, hS1, hg1, rfl⟩
      simp only [dsF, StateT.run_bind, hrun1, except_ok_bind, hgt, decide_false]
      rfl
    · rw [dcK_in (h := hc)] at h
      have hle : k ≤ HI := by
        have : ¬ hi.toNat < (r1.headD 0).toNat := fun e => hc (UInt64.lt_iff_toNat_lt.mpr e)
        simp only [decW0Nat] at hk; omega
      have hRd : RdS m m1 (· < iwTop m) := RdS.of_grow hg1
      obtain ⟨b, a', hrun, hS', hg', hr⟩ := ih m1 m' a1 (off + 1) (l - 1) xs r h hS1
        (by rw [hoff1, hl1, ← hxs, decHL]; exact decHL_agree hRd (fun j hj => by
              have := hin (j + 1) (by omega); simp only [decHL] at *; omega))
        (fun j hj => by rw [hoff1, hl1] at *; have := hin (j + 1) (by omega); have := hg1.1; omega)
      refine ⟨b, a', ?_, hS', hg1.trans hg', hr⟩
      simp only [dsF, StateT.run_bind, hrun1, except_ok_bind, hle, decide_true]
      exact hrun


/-- `nest_ds_closed` at any exec fuel. -/
def dcWf : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | n + 1, m, ctx, off, l => dcW n m ctx off l

theorem dc_spec' (p : Prog) (hf : HfF p) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hg : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL)
    (hp : p.lookup "nest_ds_closed" = some nestDsClosedL) (n : Nat) (s₀ : St) (ctx off l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ds_closed" [ctx, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ dcWf n s₀.mem ctx off l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hp]; simp only [callFn, nestDsClosedL]; vcgen [exec] <;> grind
  | succ n => exact dc_spec p hf hh hg hp n s₀ ctx off l

/-- `nest_ds_closed` from the stage relation: `ds.allM (fvarB · ≤ ctx.hiAt 0)`. -/
theorem dcWf_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) (m m' : Mem)
    (a : AState) (ctx off l : Word) (c : NestCtx) (ds : List EIdx) (r : List Word)
    (h : dcWf n m ctx off l = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hhi : c.hiAt 0 < 2 ^ 64) (hds : decHL m off.toNat l.toNat = some ds)
    (hdi : ∀ j < l.toNat, off.toNat + j < iwTop m) :
    ∃ b a', (ds.allM (dsF (c.hiAt 0))).run a = .ok (b, a') ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧
      r.headD 0 = (if b then 1 else 0) := by
  cases n with
  | zero => simp [dcWf] at h
  | succ n =>
    have hsz : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
    exact dcGoW_ok dn fe vis _ _ (by simpa using nhiW_toNat (nf := 0) hc hin hsz (by simpa using hhi)) n
      m m' a off l ds r h hS hds hdi

/-! ## `nest_walk_stack` refines `nestWalkStack` -/

def nwsK (po pl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if r.headD 0 ≠ 0 then some ([0, 0], m1) else some ([po, pl], m1)
/-- The model of `nest_walk_stack(ctx, dsOff, dsLen, progOff, progLen)` at exec fuel `n + 1`. -/
def nwsW (n : Nat) (m : Mem) (ctx off l po pl : Word) : Option (List Word × Mem) :=
  nwsK po pl (dcWf n m ctx off l)
theorem nwsK_closed (po pl : Word) (r : List Word) (m1 : Mem) (h : r.headD 0 ≠ 0) :
    nwsK po pl (some (r, m1)) = some ([0, 0], m1) := by rw [nwsK, ite_eq_left h]
theorem nwsK_open (po pl : Word) (r : List Word) (m1 : Mem) (h : ¬ r.headD 0 ≠ 0) :
    nwsK po pl (some (r, m1)) = some ([po, pl], m1) := by rw [nwsK, ite_eq_right h]
attribute [ind_grind] nwsK_closed nwsK_open

/-- The lookups of `nest_ds_closed`. -/
structure DcLook (p : Prog) : Prop where
  hf : HfF p
  hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  hg : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL
  hp : p.lookup "nest_ds_closed" = some nestDsClosedL

theorem nestWalkStack_spec (p : Prog) (hl : DcLook p)
    (hp : p.lookup "nest_walk_stack" = some nestWalkStackL) (n : Nat) (s₀ : St) (ctx off l po pl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ nwsW n s₀.mem ctx off l po pl = some (r, s'.mem); ⊤⦄ := by
  simp only [invoke_eq _ hp, callFn, nestWalkStackL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      dc_spec' p hl.hf hl.hh hl.hg hl.hp n] <;>
    finish (gen := 20) [nwsW]

theorem nestWalkStack_eq (ctx : NestCtx) (prog : List NestHole) (ds : List EIdx) :
    ConRon.Arena.nestWalkStack ctx prog ds = (do
      let closed ← ds.allM (dsF (ctx.hiAt 0))
      if closed then pure [] else pure prog) := rfl

theorem nwsW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) (m m' : Mem)
    (a : AState) (ctx off l po pl : Word) (c : NestCtx) (ds : List EIdx) (prog : List NestHole)
    (r : List Word) (h : nwsW n m ctx off l po pl = some (r, m')) (hS : StageR dn vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hhi : c.hiAt 0 < 2 ^ 64) (hds : decHL m off.toNat l.toNat = some ds)
    (hdi : ∀ j < l.toNat, off.toNat + j < iwTop m) :
    ∃ x a', (ConRon.Arena.nestWalkStack c prog ds).run a = .ok (x, a') ∧ StageR dn vis fe m' a' ∧
      IWGrow m m' ∧ ((x = [] ∧ r = [0, 0]) ∨ (x = prog ∧ r = [po, pl])) := by
  unfold nwsW at h
  rcases hd : dcWf n m ctx off l with _ | ⟨r1, m1⟩ <;> rw [hd] at h; · simp [nwsK] at h
  obtain ⟨b, a', hrun, hS', hg, hr⟩ := dcWf_ok dn fe vis n m m1 a ctx off l c ds r1 hd hS hc hin hhi hds hdi
  rw [nestWalkStack_eq]
  cases b with
  | true =>
    rw [nwsK_closed (h := by rw [hr]; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a', ?_, hS', hg, Or.inl ⟨rfl, rfl⟩⟩
    simp only [StateT.run_bind, hrun, except_ok_bind]; rfl
  | false =>
    rw [nwsK_open (h := by rw [hr]; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨prog, a', ?_, hS', hg, Or.inr ⟨rfl, rfl⟩⟩
    simp only [StateT.run_bind, hrun, except_ok_bind]; rfl

section census
variable (p : Prog) (hl : DcLook p) (hp : p.lookup "nest_walk_stack" = some nestWalkStackL)
include hl hp

/-- **`nest_walk_stack` refines `nestWalkStack`** (through the `fvar_b` stub; the ctx's `hiAt 0`
below `2^64`): the empty stack `(0, 0)` or the given one. -/
@[refines ConRon.Arena.nestWalkStack]
theorem nestWalkStack_refines (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis ctx off l po pl : Word) (c : NestCtx) (ds : List EIdx) (prog : List NestHole)
    (hS : StageR dn vis fe s₀.mem a₀) (hc : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hhi : c.hiAt 0 < 2 ^ 64)
    (hds : decHL s₀.mem off.toNat l.toNat = some ds) (hdi : ∀ j < l.toNat, off.toNat + j < iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestWalkStack c prog ds) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestWalkStack c prog ds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      ((AM.res (ConRon.Arena.nestWalkStack c prog ds) a₀ = [] ∧ r = [0, 0]) ∨
        (AM.res (ConRon.Arena.nestWalkStack c prog ds) a₀ = prog ∧ r = [po, pl])); ⊤⦄ := by
  refine triple_post (nestWalkStack_spec p hl hp n s₀ ctx off l po pl) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nwsW_ok dn fe vis n _ _ a₀ ctx off l po pl c ds prog r hm hS hc
    hin hhi hds hdi
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census


/-! ## `pi_doms_occ` refines `piDomsOcc` -/

/-- `nest_occ` at any exec fuel. -/
def noConstWf : Nat → Mem → Word → Word → Word → Word → Word → Option (Word × Mem)
  | 0, _, _, _, _, _, _ => none
  | n + 1, m, no, nl, lo, hi, e => noConstW n m no nl lo hi e

/-- The lookups of `nest_occ`. -/
structure NoLook (p : Prog) : Prop where
  hv : p.lookup "e_view" = some eView
  hc : p.lookup "sl_contains" = some slContains
  hf : p.lookup "no_find" = some (memoFindG noSch)
  hput : p.lookup "no_put" = some (memoPutG noSch)
  hgo : p.lookup "nest_occ_go" = some nestOccGo
  hnode : p.lookup "nest_occ_node" = some nestOccNode
  hcl : p.lookup "no_clear" = some (memoClearG noSch)
  hp : p.lookup "nest_occ" = some nestOcc

theorem nestOcc_spec' (p : Prog) (hl : NoLook p) (n : Nat) (s₀ : St) (no nl lo hi e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_occ" [no, nl, lo, hi, e]
    ⦃fun r s' => LocEq s' s₀ ∧ noConstWf n s₀.mem no nl lo hi e = some (r.headD 0, s'.mem); ⊤⦄ := by
  cases n with
  | zero => rw [invoke_eq _ hl.hp]; simp only [callFn, nestOcc]; vcgen [exec] <;> grind
  | succ n => exact nestOcc_spec p hl.hv hl.hc hl.hf hl.hput hl.hgo hl.hnode hl.hcl hl.hp n s₀ no nl lo hi e

/-- `nest_occ` from the stage relation, its names a decoded slice below the top. -/
theorem noConstWf_ok (n : Nat) (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word)
    (m m' : Mem) (a : AState) (no nl lo hi e r : Word) (names : List NIdx) (mp0 : Std.HashMap EIdx Bool)
    (hb : noConstWf n m no nl lo hi e = some (r, m')) (hS : StageR dn vis fe m a) (hh : H e)
    (hn : decHL m no.toNat nl.toNat = some names) (hnb : no.toNat + nl.toNat < 2 ^ 64)
    (hM : noMR m mp0) :
    ∃ b, (ConRon.Arena.nestOcc names lo.toNat hi.toNat (decE e)).run a = .ok (b, a) ∧ (r != 0) = b ∧
      noMR m' ∅ ∧ StageR dn vis fe m' a ∧ IWGrow m m' ∧ MFr [NOM] [204, 205] m m' := by
  cases n with
  | zero => simp [noConstWf] at hb
  | succ n =>
    obtain ⟨ws, hws, rfl, hwlt⟩ := slR_of_decHL m nl.toNat no.toNat names hn hnb
    simp only [UInt64.ofNat_toNat] at hws
    exact noConstW_ok n dn fe vis m m' a no nl lo hi e r ws mp0 hb hS hh hws hwlt hM

mutual
def pdoW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, no, nl, lo, hi, n, e =>
    if n = 0 then some ([0], m)
    else if e >>> 28 ≠ 6 then some ([0], m)
    else if eViewW m e = [] then none
    else pdoK1 k no nl lo hi n (eViewW m e) (noConstWf k m no nl lo hi ((eViewW m e).tail.headD 0))
def pdoK1 (k : Nat) (no nl lo hi n : Word) (v : List Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r ≠ 0 then some ([1], m1) else pdoW k m1 no nl lo hi (n - 1) (v.tail.tail.headD 0)
end

section arms
variable (k : Nat) (m m1 : Mem) (no nl lo hi n e r : Word) (v : List Word)
theorem pdoW_zero (h : n = 0) : pdoW (k + 1) m no nl lo hi n e = some ([0], m) := by simp [pdoW, h]
theorem pdoW_notpi (h : ¬ n = 0) (h6 : e >>> 28 ≠ 6) : pdoW (k + 1) m no nl lo hi n e = some ([0], m) := by
  simp [pdoW, h, h6]
theorem pdoW_empty (h : ¬ n = 0) (h6 : ¬ e >>> 28 ≠ 6) (hv : eViewW m e = []) :
    pdoW (k + 1) m no nl lo hi n e = none := by
  simp only [pdoW]; rw [ite_eq_right h, ite_eq_right h6, ite_eq_left hv]
theorem pdoW_pi (h : ¬ n = 0) (h6 : ¬ e >>> 28 ≠ 6) (hv : eViewW m e ≠ []) : pdoW (k + 1) m no nl lo hi n e =
    pdoK1 k no nl lo hi n (eViewW m e) (noConstWf k m no nl lo hi ((eViewW m e).tail.headD 0)) := by
  simp only [pdoW]; rw [ite_eq_right h, ite_eq_right h6, ite_eq_right hv]
theorem pdoK1_hit (h : r ≠ 0) : pdoK1 k no nl lo hi n v (some (r, m1)) = some ([1], m1) := by
  rw [pdoK1, ite_eq_left h]
theorem pdoK1_miss (h : ¬ r ≠ 0) : pdoK1 k no nl lo hi n v (some (r, m1)) =
    pdoW k m1 no nl lo hi (n - 1) (v.tail.tail.headD 0) := by rw [pdoK1, ite_eq_right h]
end arms
attribute [ind_grind] pdoW_zero pdoW_notpi pdoW_empty pdoW_pi pdoK1_hit pdoK1_miss

theorem piDomsOcc_spec (p : Prog) (hl : NoLook p) (hp : p.lookup "pi_doms_occ" = some piDomsOccL)
    (k : Nat) : ∀ (s₀ : St) (no nl lo hi n e : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "pi_doms_occ" [no, nl, lo, hi, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧ pdoW k s₀.mem no nl lo hi n e = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ no nl lo hi n e
    rw [invoke_eq _ hp]; simp only [callFn, piDomsOccL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ no nl lo hi n e
    simp only [invoke_eq _ hp, callFn, piDomsOccL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        eView_spec p hl.hv k, nestOcc_spec' p hl k, ih] <;>
      finish (gen := 20)

theorem pdoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis no nl lo hi : Word)
    (names : List NIdx) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (n e : Word) (r : List Word) (mp : Std.HashMap EIdx Bool),
    pdoW k m no nl lo hi n e = some (r, m') → StageR dn vis fe m a → H e →
    decHL m no.toNat nl.toNat = some names → (∀ j < nl.toNat, no.toNat + j < iwTop m) →
    noMR m mp →
    ∃ b a' mp', (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)).run a = .ok (b, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ noMR m' mp' ∧
      MFr [NOM] [204, 205] m m' := by
  induction k with
  | zero => intro m m' a n e r mp h; simp [pdoW] at h
  | succ k ih =>
    intro m m' a n e r mp h hS he hn hnb hM
    by_cases h0 : n = 0
    · rw [pdoW_zero (h := h0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst h0
      exact ⟨false, a, mp, rfl, hS, IWGrow.refl _, rfl, hM, MFr.refl _ _ _⟩
    have hn0 : n.toNat ≠ 0 := fun e' => h0 (UInt64.toNat_inj.mp (by simpa using e'))
    have hsucc : n.toNat = (n.toNat - 1) + 1 := by omega
    by_cases h6 : e >>> 28 ≠ 6
    · rw [pdoW_notpi (h := h0) (h6 := h6)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a, mp, ?_, hS, IWGrow.refl _, rfl, hM, MFr.refl _ _ _⟩
      have htag : ¬ (decE e).tag = ETag.forallE := fun h' => h6 ((decE_tag_forall e he).mp h')
      rw [hsucc, ConRon.Arena.piDomsOcc.eq_2]
      simp [htag]; rfl
    have hg6 : e >>> 28 = 6 := by simpa using h6
    have hR := hS.1.arena.1
    by_cases hr : eViewW m e = []
    · rw [pdoW_empty (h := h0) (h6 := h6) (hv := hr)] at h; simp at h
    rw [pdoW_pi (h := h0) (h6 := h6) (hv := hr)] at h
    obtain ⟨hvok, hew⟩ := eViewW_forall m e hg6 hr
    obtain ⟨-, hty, hb⟩ := view_forall m a hR e he hvok hg6
    have hvb := viewBind_forall m a hR e he hvok hg6
    simp only [hew, List.tail_cons, List.headD_cons] at h
    generalize hd : tfld m FORALL (tierW e) (idxW e) 0 = d at h hty hvb
    generalize hbd : tfld m FORALL (tierW e) (idxW e) 1 = b at h hb hvb
    rcases hnc : noConstWf k m no nl lo hi d with _ | ⟨r1, m1⟩ <;> rw [hnc] at h; · simp [pdoK1] at h
    have hnb' : no.toNat + nl.toNat < 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos nl.toNat with hz | hz
      · rw [hz]; simpa using no.toNat_lt
      · have := hnb (nl.toNat - 1) (by omega); have := hS.2.1; have := hS.2.2.2.1; omega
    obtain ⟨c, hrun1, hc, hM1, hS1, hg1, hf1⟩ := noConstWf_ok k dn fe vis m m1 a no nl lo hi d r1 names mp hnc
      hS hty hn hnb' hM
    have hpre : (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)).run a =
        (do let x ← ConRon.Arena.nestOcc names lo.toNat hi.toNat (decE d)
            if x = true then pure true
            else ConRon.Arena.piDomsOcc names lo.toNat hi.toNat (n.toNat - 1) (decE b)).run a := by
      rw [hsucc, ConRon.Arena.piDomsOcc.eq_2]
      have htag : (decE e).tag = ETag.forallE := (decE_tag_forall e he).mpr hg6
      simp only [htag, beq_self_eq_true, ite_true, StateT.run_bind, viewBind_run' _ a, hvb, except_ok_bind]
      rfl
    by_cases hr1 : r1 ≠ 0
    · rw [pdoK1_hit (h := hr1)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hcT : c = true := by rw [← hc]; simpa using hr1
      subst hcT
      refine ⟨true, a, ∅, ?_, hS1, hg1, rfl, hM1, hf1⟩
      rw [hpre]; simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
    · rw [pdoK1_miss (h := hr1)] at h
      simp only [List.tail_cons, List.headD_cons] at h
      have hcF : c = false := by rw [← hc]; simpa using hr1
      subst hcF
      have hn1 : (n - 1).toNat = n.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      obtain ⟨b', a', mp', hrun, hS', hg', hr', hM', hf'⟩ := ih m1 m' a (n - 1) b r ∅ h hS1 hb
        (by rw [decHL_agree (RdS.of_grow hg1) hnb]; exact hn)
        (fun j hj => Nat.lt_of_lt_of_le (hnb j hj) hg1.1) hM1
      refine ⟨b', a', mp', ?_, hS', hg1.trans hg', hr', hM', hf1.trans hf'⟩
      rw [hpre]; simp only [StateT.run_bind, hrun1, except_ok_bind]
      rw [← hn1]; exact hrun

section census
variable (p : Prog) (hl : NoLook p) (hp : p.lookup "pi_doms_occ" = some piDomsOccL)
include hl hp

/-- **`pi_doms_occ` refines `piDomsOcc`** (the `nest_occ` memo well-formed on entry). -/
@[refines ConRon.Arena.piDomsOcc]
theorem piDomsOcc_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lo hi n e : Word) (names : List NIdx) (mp : Std.HashMap EIdx Bool)
    (hS : StageR dn vis fe s₀.mem a₀) (he : H e) (hn : decHL s₀.mem no.toNat nl.toNat = some names)
    (hnb : ∀ j < nl.toNat, no.toNat + j < iwTop s₀.mem) (hM : noMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "pi_doms_occ" [no, nl, lo, hi, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      r.headD 0 = (if AM.res (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)) a₀
        then 1 else 0) ∧ ∃ mp', noMR s'.mem mp'; ⊤⦄ := by
  refine triple_post (piDomsOcc_spec p hl hp k s₀ no nl lo hi n e) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨b, a', mp', hrun, hS', hg, hr, hM', -⟩ := pdoW_ok dn fe vis no nl lo hi names k _ _ a₀ n e _ mp hm hS
    he hn hnb hM
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hst]; exact hS', hg, by rw [hres]; simpa using hr, mp', hM'⟩

end census

/-! ## `nest_group_ctors` refines `nestGroupCtors` -/

/-- `nest_container` at any exec fuel. -/
def ntWf : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | k + 1, m, vis, C => ntW k m vis C

theorem nt_spec' (p : Prog) (hl : NtLook p) (k : Nat) (s₀ : St) (vis C : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_container" [vis, C]
    ⦃fun r s' => LocEq s' s₀ ∧ ntWf k s₀.mem vis C = some (r, s'.mem); ⊤⦄ := by
  cases k with
  | zero => rw [invoke_eq _ hl.hnt]; simp only [callFn, nestContainer]; vcgen [exec] <;> grind
  | succ k => exact nt_spec p hl k s₀ vis C

mutual
def gcW : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | k + 1, m, vis, nPc, off, l, oo, ol =>
    if l = 0 then some ([oo, ol], m)
    else gcK1 k vis nPc off l oo ol (ntWf k m vis (rdW (m.arr64 IW) off))
def gcK1 (k : Nat) (vis nPc off l oo ol : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then none
    else if r.tail.headD 0 ≠ nPc then
      (if r.tail.tail.tail.headD 0 ≠ 0 then none
       else gcK2 k vis nPc off l (appendW k m1 oo ol (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)))
    else gcK2 k vis nPc off l (appendW k m1 oo ol (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0))
def gcK2 (k : Nat) (vis nPc off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => gcW k m2 vis nPc (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0)
end

section arms
variable (k : Nat) (m m1 m2 : Mem) (vis nPc off l oo ol : Word) (r r2 : List Word)
theorem gcW_nil (h : l = 0) : gcW (k + 1) m vis nPc off l oo ol = some ([oo, ol], m) := by simp [gcW, h]
theorem gcW_cons (h : ¬ l = 0) : gcW (k + 1) m vis nPc off l oo ol =
    gcK1 k vis nPc off l oo ol (ntWf k m vis (rdW (m.arr64 IW) off)) := by simp [gcW, h]
theorem gcK1_none (h : r.headD 0 = 0) : gcK1 k vis nPc off l oo ol (some (r, m1)) = none := by
  rw [gcK1, ite_eq_left h]
theorem gcK1_bad (h : ¬ r.headD 0 = 0) (h1 : r.tail.headD 0 ≠ nPc) (h3 : r.tail.tail.tail.headD 0 ≠ 0) :
    gcK1 k vis nPc off l oo ol (some (r, m1)) = none := by rw [gcK1, ite_eq_right h, ite_eq_left h1, ite_eq_left h3]
theorem gcK1_empty (h : ¬ r.headD 0 = 0) (h1 : r.tail.headD 0 ≠ nPc) (h3 : ¬ r.tail.tail.tail.headD 0 ≠ 0) :
    gcK1 k vis nPc off l oo ol (some (r, m1)) =
      gcK2 k vis nPc off l (appendW k m1 oo ol (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)) := by
  rw [gcK1, ite_eq_right h, ite_eq_left h1, ite_eq_right h3]
theorem gcK1_same (h : ¬ r.headD 0 = 0) (h1 : ¬ r.tail.headD 0 ≠ nPc) :
    gcK1 k vis nPc off l oo ol (some (r, m1)) =
      gcK2 k vis nPc off l (appendW k m1 oo ol (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)) := by
  rw [gcK1, ite_eq_right h, ite_eq_right h1]
theorem gcK2_some : gcK2 k vis nPc off l (some (r2, m2)) =
    gcW k m2 vis nPc (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) := by rw [gcK2]
end arms
attribute [ind_grind] gcW_nil gcW_cons gcK1_none gcK1_bad gcK1_empty gcK1_same gcK2_some

theorem nestGroupCtors_spec (p : Prog) (hl : NtLook p) (hc : p.lookup "iw_copy" = some iwCopy)
    (hap : p.lookup "sl_append" = some slAppend)
    (hp : p.lookup "nest_group_ctors" = some nestGroupCtorsL) (k : Nat) :
    ∀ (s₀ : St) (vis nPc off l oo ol : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_group_ctors" [vis, nPc, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧
      gcW k s₀.mem vis nPc off l oo ol = some ([r.headD 0, r.tail.headD 0], s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ vis nPc off l oo ol
    rw [invoke_eq _ hp]; simp only [callFn, nestGroupCtorsL]; vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ vis nPc off l oo ol
    simp only [invoke_eq _ hp, callFn, nestGroupCtorsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        nt_spec' p hl k, slAppend_specW p hl.ha hc hap k, ih] <;>
      finish (gen := 20) [rdW_eq]

theorem CNOk.grow {m m' : Mem} {p : Nat} {x : IConstantVal × Nat} (h : CNOk m p x (· < iwTop m))
    (hg : IWGrow m m') : CNOk m' p x (· < iwTop m') :=
  (h.agree (RdS.of_grow hg) (GrowX.of_grow (q := 0) (n := 0) hg).erecP).mono
    fun _ hx => Nat.lt_of_lt_of_le hx hg.1

theorem gcW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis nPc : Word)
    (k : Nat) : ∀ (m m' : Mem) (a : AState) (off l oo ol : Word) (cs : List NIdx)
      (out : List (IConstantVal × Nat)) (r : List Word),
    gcW k m vis nPc off l oo ol = some (r, m') → StageR dn vis fe m a →
    decHL m off.toNat l.toNat = some cs → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ol.toNat = out.length → oo.toNat + out.length ≤ iwTop m → CsAt m oo.toNat out (· < iwTop m) →
    ∃ res a', (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out).run a = .ok (res, a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.tail.headD 0).toNat = res.length ∧
      (r.headD 0).toNat + res.length ≤ iwTop m' ∧ CsAt m' (r.headD 0).toNat res (· < iwTop m') := by
  induction k with
  | zero => intro m m' a off l oo ol cs out r h; simp [gcW] at h
  | succ k ih =>
    intro m m' a off l oo ol cs out r h hS hcs' hcb hol hob hout
    by_cases hl0 : l = 0
    · rw [gcW_nil (h := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : cs = [] := by simpa [decHL, hslice?] using hcs'.symm
      subst this
      exact ⟨out, a, by simp [ConRon.Arena.nestGroupCtors]; rfl, hS, IWGrow.refl _, by simpa using hol,
        by simpa using hob, by simpa using hout⟩
    rw [gcW_cons (h := hl0)] at h
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hcs2 := hcs'
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hcs2
    obtain ⟨c, hc, cs', hcs'', rfl⟩ := hcs2
    obtain ⟨hcH, hcd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.name) (by simpa [iwH, iwA] using hc)
    have hsz := hS.2.2.2.1
    have htop : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hsz
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hcb 0 (by omega); omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    cases k with
    | zero => simp [ntWf, gcK1] at h
    | succ k =>
    simp only [ntWf] at h
    rcases hnt : ntW k m vis (rdW (m.arr64 IW) off) with _ | ⟨r1, m1⟩ <;> rw [hnt] at h; · simp [gcK1] at h
    obtain ⟨x, a1, hrun1, hS1, hg1, hnc⟩ := ntW_ok dn fe vis _ hcH k m m1 a r1 hnt hS
    rw [hcd] at hrun1
    cases x with
    | none =>
      have : r1.headD 0 = 0 := hnc
      rw [gcK1_none (h := this)] at h; simp at h
    | some pc =>
    obtain ⟨nPc2, ctors⟩ := pc
    obtain ⟨h0, h1, h3, h2b, hcs3⟩ := hnc
    have hne0 : ¬ r1.headD 0 = 0 := by rw [h0]; decide
    -- the parameter-count check, and the append
    have hok : ∀ (r2 : List Word) (m2 : Mem),
        appendW (k + 1) m1 oo ol (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) = some (r2, m2) →
        gcW (k + 1) m2 vis nPc (off + 1) (l - 1) (r2.headD 0) (r2.tail.headD 0) = some (r, m') →
        (nPc2 == nPc.toNat || ctors.length == 0) = true →
        ∃ res a', (ConRon.Arena.nestGroupCtors fe nPc.toNat (c :: cs') out).run a = .ok (res, a') ∧
          StageR dn vis fe m' a' ∧ IWGrow m m' ∧ (r.tail.headD 0).toNat = res.length ∧
          (r.headD 0).toNat + res.length ≤ iwTop m' ∧ CsAt m' (r.headD 0).toNat res (· < iwTop m') := by
      intro r2 m2 hap hrec hchk
      obtain ⟨hS2, hg2, hr20, hr21, ht2, hw1, hw2⟩ := appendW_stage hap hS1 (by have := hg1.1; omega)
        (by rw [h3]; exact h2b)
      rw [h3] at hr21 ht2 hw2
      have hcsA : CsAt m2 (r2.headD 0).toNat (out ++ ctors) (· < iwTop m2) := by
        intro i hi
        rw [hr20]
        by_cases hio : i < out.length
        · obtain ⟨w, hw, hc'⟩ := hout i hio
          refine ⟨w, ?_, ?_⟩
          · rw [hw1 i (by omega), hg1.2.2.1 _ (by omega)]; exact hw
          · rw [List.getElem_append_left hio]; exact (hc'.grow hg1).grow hg2
        · simp only [List.length_append] at hi
          obtain ⟨w, hw, hc'⟩ := hcs3 (i - out.length) (by omega)
          refine ⟨w, ?_, ?_⟩
          · have := hw2 (i - out.length) (by omega)
            rw [show iwTop m1 + ol.toNat + (i - out.length) = iwTop m1 + i by omega] at this
            rw [this]; exact hw
          · rw [List.getElem_append_right (by omega)]; exact hc'.grow hg2
      obtain ⟨res, a', hrun, hS', hg', h1', h2', h3'⟩ := ih m2 m' a1 (off + 1) (l - 1) (r2.headD 0)
        (r2.tail.headD 0) cs' (out ++ ctors) r hrec hS2
        (by rw [hoff1, hl1, decHL_agree (RdS.of_grow (hg1.trans hg2)) (fun j hj => by
              have := hcb (j + 1) (by omega); omega)]
            simpa [decHL] using hcs'')
        (fun j hj => by rw [hoff1, hl1] at *; have := hcb (j + 1) (by omega); have := hg1.1; have := hg2.1; omega)
        (by rw [hr21]; simp [hol]) (by rw [hr20]; simp; omega) hcsA
      refine ⟨res, a', ?_, hS', (hg1.trans hg2).trans hg', h1', h2', h3'⟩
      simp only [ConRon.Arena.nestGroupCtors.eq_2, StateT.run_bind, hrun1, except_ok_bind, hchk, Bool.not_true]
      exact hrun
    by_cases hp1 : r1.tail.headD 0 ≠ nPc
    · have hneq : nPc2 ≠ nPc.toNat := fun e => hp1 (UInt64.toNat_inj.mp (by rw [h1, e]))
      by_cases hp3 : r1.tail.tail.tail.headD 0 ≠ 0
      · rw [gcK1_bad (h := hne0) (h1 := hp1) (h3 := hp3)] at h; simp at h
      rw [gcK1_empty (h := hne0) (h1 := hp1) (h3 := hp3)] at h
      have hlen0 : ctors.length = 0 := by rw [← h3, show r1.tail.tail.tail.headD 0 = 0 by simpa using hp3]; rfl
      rcases hap : appendW (k + 1) m1 oo ol (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [hap] at h; · simp [gcK2] at h
      rw [gcK2_some] at h
      exact hok r2 m2 hap h (by simp [hlen0])
    · have heq : nPc2 = nPc.toNat := by rw [← h1, show r1.tail.headD 0 = nPc by simpa using hp1]
      rw [gcK1_same (h := hne0) (h1 := hp1)] at h
      rcases hap : appendW (k + 1) m1 oo ol (r1.tail.tail.headD 0) (r1.tail.tail.tail.headD 0) with _ | ⟨r2, m2⟩ <;> rw [hap] at h; · simp [gcK2] at h
      rw [gcK2_some] at h
      exact hok r2 m2 hap h (by simp [heq])

section census
variable (p : Prog) (hl : NtLook p) (hc : p.lookup "iw_copy" = some iwCopy)
  (hap : p.lookup "sl_append" = some slAppend)
  (hp : p.lookup "nest_group_ctors" = some nestGroupCtorsL)
include hl hc hap hp

/-- **`nest_group_ctors` refines `nestGroupCtors`** (through `nest_container`'s stubs). -/
@[refines ConRon.Arena.nestGroupCtors]
theorem nestGroupCtors_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis nPc off l oo ol : Word) (cs : List NIdx) (out : List (IConstantVal × Nat))
    (hS : StageR dn vis fe s₀.mem a₀)
    (hcs' : decHL s₀.mem off.toNat l.toNat = some cs) (hcb : ∀ j < l.toNat, off.toNat + j < iwTop s₀.mem)
    (hol : ol.toNat = out.length) (hob : oo.toNat + out.length ≤ iwTop s₀.mem)
    (hout : CsAt s₀.mem oo.toNat out (· < iwTop s₀.mem)) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "nest_group_ctors" [vis, nPc, off, l, oo, ol]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      (r.tail.headD 0).toNat = (AM.res (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀).length ∧
      (r.headD 0).toNat + (AM.res (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀).length ≤ iwTop s'.mem ∧
      CsAt s'.mem (r.headD 0).toNat (AM.res (ConRon.Arena.nestGroupCtors fe nPc.toNat cs out) a₀)
        (· < iwTop s'.mem); ⊤⦄ := by
  refine triple_post (nestGroupCtors_spec p hl hc hap hp k s₀ vis nPc off l oo ol) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨res, a', hrun, hS', hg, h1, h2, h3⟩ := gcW_ok dn fe vis nPc k _ _ a₀ off l oo ol cs out _ hm hS
    hcs' hcb hol hob hout
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  refine ⟨hlc, hok, by rw [hst]; exact hS', hg, ?_, ?_, ?_⟩
  · rw [hres]; simpa using h1
  · rw [hres]; exact h2
  · rw [hres]; exact h3

end census

end L.Ind
