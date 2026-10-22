import ConAgua.Arena.IndPosSpec2
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndDecStab

/-! # `IndPos2`'s leaves (lane `indproofs2`, helper `pos`, fork E)

`nestArity`, … — the template of `IndPosSpec2.lean`. -/

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
    cases hrec : piBW n m (fuel - 1) ((eViewW m h).getD 2 0) with
    | none => rw [hrec] at hpb; simp [piBK2] at hpb
    | some rm =>
    obtain ⟨rs1, m1⟩ := rm
    rw [hrec, piBK2_some] at hpb
    cases hcons : consW n m1 ((eViewW m h).getD 1 0) (rs1.headD 0) (rs1.getD 1 0) with
    | none => rw [hcons] at hpb; simp [piBK3] at hpb
    | some rm2 =>
    obtain ⟨r2, m2⟩ := rm2
    rw [hcons, piBK3_some] at hpb
    simp only [Option.some.injEq, Prod.mk.injEq] at hpb
    obtain ⟨-, rfl⟩ := hpb
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
theorem naK1_miss (h : r.headD 0 = 0) : naK1 n (some (r, m1)) = some ([0], m1) := by rw [naK1, if_pos h]
theorem naK1_noind (h : ¬ r.headD 0 = 0) (h3 : rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    naK1 n (some (r, m1)) = some ([0], m1) := by rw [naK1, if_neg h, if_pos h3]
theorem naK1_ind (h : ¬ r.headD 0 = 0) (h3 : ¬ rdW (m1.arr64 EREC) (r.tail.headD 0) ≠ 3) :
    naK1 n (some (r, m1)) = naK2 (piBW n m1 CWF (rdW (m1.arr64 EREC) (r.tail.headD 0 + 4))) := by
  rw [naK1, if_neg h, if_neg h3]
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
  rw [invoke_eq _ hl.hp]
  simp only [callFn, nestArityL]
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
  cases hef : envFindW m C vis with
  | none => rw [hef] at h; simp [naK1] at h
  | some pr =>
  obtain ⟨r1, m1⟩ := pr
  rw [hef] at h
  have hm1 := envFindW_mem hef
  rw [hm1] at h hef
  by_cases hf0 : r1.headD 0 = 0
  · rw [naK1_miss (h := hf0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, hfind⟩ := envFindW_miss hef hE hC hf0
    refine ⟨0, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestArity_none (fun cv caps e => by rw [hfind] at e; cases e)]; rfl
  obtain ⟨-, hfind, ci, hci⟩ := envFindW_hit hef hE hC hf0
  rw [hci] at hfind
  have hciq := decCI_idx hci
  have hsz := erecP_size_le m
  by_cases h3 : rdW (m.arr64 EREC) (r1.tail.headD 0) ≠ 3
  · rw [naK1_noind (h := hf0) (h3 := h3)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
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
  cases hpb : piBW n m CWF w with
  | none => rw [hpb] at h; simp [naK2] at h
  | some pr =>
  obtain ⟨rs, m2⟩ := pr
  rw [hpb, naK2_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
def hiW (m : Mem) (ctx nf : Word) : Word := rdW (m.arr64 IW) (ctx + 4) + rdW (m.arr64 IW) (ctx + 1) + nf

theorem nestCtxHiAt_specW (p : Prog) (hp : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt) (n : Nat)
    (s₀ : St) (ctx nf : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ctx_hi_at" [ctx, nf]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r.headD 0 = hiW s₀.mem ctx nf; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestCtxHiAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [hiW, rdW_eq]

theorem hiW_toNat {m : Mem} {ctx nf : Word} {c : NestCtx} (hc : decCtx m ctx.toNat = some c)
    (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsz : iwTop m < 2 ^ 64)
    (hhi : c.hiAt nf.toNat < 2 ^ 64) : (hiW m ctx nf).toNat = c.hiAt nf.toNat := by
  obtain ⟨hn, -, -, -, hnP, -⟩ := ctx_fields hc hin hsz
  have hl := decHL_length m hn
  simp only [NestCtx.hiAt] at hhi ⊢
  simp only [hiW]
  rw [UInt64.toNat_add, UInt64.toNat_add, hnP, hl]
  omega

/-- A decoded handle at `o`, as the word L reads there. -/
theorem rd_iwH0 {k : IdxKind} {m : Mem} {o : Word} {x : Idx k} (h : iwH m o.toNat = some x) :
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
    else dcK n hi off l (stubM "fvar_b" m [CWF, rdW (m.arr64 IW) off])
def dcK (n : Nat) (hi off l : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) => if hi < r.headD 0 then some ([0], m1) else dcGoW n m1 hi (off + 1) (l - 1)
end

section arms
variable (n : Nat) (m m1 : Mem) (hi off l : Word) (r : List Word)
theorem dcGoW_nil (h : l = 0) : dcGoW (n + 1) m hi off l = some ([1], m) := by simp [dcGoW, h]
theorem dcGoW_cons (h : ¬ l = 0) : dcGoW (n + 1) m hi off l =
    dcK n hi off l (stubM "fvar_b" m [CWF, rdW (m.arr64 IW) off]) := by simp [dcGoW, h]
theorem dcK_out (h : hi < r.headD 0) : dcK n hi off l (some (r, m1)) = some ([0], m1) := by
  rw [dcK, if_pos h]
theorem dcK_in (h : ¬ hi < r.headD 0) : dcK n hi off l (some (r, m1)) = dcGoW n m1 hi (off + 1) (l - 1) := by
  rw [dcK, if_neg h]
end arms
attribute [ind_grind] dcGoW_nil dcGoW_cons dcK_out dcK_in

theorem dcGo_spec (p : Prog) (hp : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL) (n : Nat) :
    ∀ (s₀ : St) (hi off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "nest_ds_closed_go" [hi, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ dcGoW n s₀.mem hi off l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ hi off l
    rw [invoke_eq _ hp]; simp only [callFn, nestDsClosedGoL]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ hi off l
    rw [invoke_eq _ hp]
    simp only [callFn, nestDsClosedGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        stubM_spec p "fvar_b" n, ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The model of `nest_ds_closed(ctx, off, l)` at exec fuel `n + 1`. -/
def dcW (n : Nat) (m : Mem) (ctx off l : Word) : Option (List Word × Mem) := dcGoW n m (hiW m ctx 0) off l

theorem dc_spec (p : Prog) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hg : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL)
    (hp : p.lookup "nest_ds_closed" = some nestDsClosedL) (n : Nat) (s₀ : St) (ctx off l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_ds_closed" [ctx, off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ dcW n s₀.mem ctx off l = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, nestDsClosedL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      nestCtxHiAt_specW p hh n, dcGo_spec p hg n] <;>
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
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hl0
      have : ds = [] := by simpa [decHL, hslice?] using hds.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl⟩
    rw [dcGoW_cons (h := hl0)] at h
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hds' := hds
    simp only [decHL] at hds'
    rw [hl', hslice?_succ] at hds'
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hds'
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hds'
    obtain ⟨hxH, hxd⟩ := rd_iwH0 (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA] using hx)
    have hsz := hS.2.2.2.1
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      word_add_toNat (show off.toNat + 1 < 2 ^ 64 by have := hin 0 (by omega); have := hS.2.1; omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    cases hst : stubM "fvar_b" m [CWF, rdW (m.arr64 IW) off] with
    | none => rw [hst] at h; simp [dcK] at h
    | some pr =>
    obtain ⟨r1, m1⟩ := pr
    rw [hst] at h
    obtain ⟨k, a1, hrun1, hS1, hg1, hk⟩ := fvarB_spec dn vis fe CWF _ hxH _ _ a r1 hst hS
    rw [CWF_eq, hxd] at hrun1
    rw [List.allM_cons]
    by_cases hc : hi < r1.headD 0
    · rw [dcK_out (h := hc)] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
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

end L.Ind
