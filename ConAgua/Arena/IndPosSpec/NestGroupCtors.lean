module

public import ConAgua.Arena.IndPosSpec.NcGoW
public import ConAgua.Arena.IndPosSpec.NoConstWf
public import ConAgua.Arena.GrindAttr
public import ConAgua.Arena.IndGrindAttr
public import ConAgua.L.GrindAttr
import all Init.Data.List.Control
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.IndPos
import all ConAgua.Arena.IndPos2
import ConAgua.L.ModelGen
import ConAgua.Arena.IndPosSpec.BvbWMfr
import ConAgua.L.WordOff
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# NestGroupCtors: `ConRon.Arena.nestGroupCtors`, `ConRon.Arena.nestWalkStack`, `ConRon.Arena.piDomsOcc`

The refinement theorems `nestWalkStack_refines`, `piDomsOcc_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

theorem nhiW_toNat {m : Mem} {ctx nf : Word} {c : NestCtx} (hc : decCtx m ctx.toNat = some c)
    (hin : CtxIn m ctx.toNat (· < iwTop m)) (hsz : iwTop m < 2 ^ 64)
    (hhi : c.hiAt nf.toNat < 2 ^ 64) : (nhiW m ctx nf).toNat = c.hiAt nf.toNat := by
  obtain ⟨hn, -, -, -, hnP, -⟩ := ctx_fields hc hin hsz
  have hl := decHL_length m hn
  simp only [NestCtx.hiAt] at hhi ⊢
  simp only [nhiW, UInt64.toNat_add, hnP, hl]
  omega

/-! ## `nest_container`: model, spec and refinement -/

section
-- the steps' `grind` would otherwise unfold `env_find`'s model while comparing the record reads
attribute [local irreducible] findRes

l_model nt_spec' (p : Prog) (hl : NtLook p)
  fns [hl.hnt ↦ ntWf list]
  specs [envFind_spec p hl.hg hl.hb hl.hf n, nc_spec p hl n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

end

theorem ntW_ok (fe : IFEnv) (vis C : Word) (hC : H C)
    (k : Nat) (m m' : Mem) (a : AState) (r : List Word)
    (h : ntWf (k + 1) m vis C = some (r, m')) (hS : StageR vis fe m a) :
    ∃ x a', (ConRon.Arena.nestContainer fe (decI C)).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ NcOut m' r x := by
  have hE := hS.check.env
  by_cases hf0 : (findRes m vis C).headD 0 = 0
  · rw [ntWf.arm1 (hc1 := hf0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hfind := findRes_miss hE hC hf0
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestContainer_none (fun cv caps e => by rw [hfind] at e; cases e)]; rfl
  obtain ⟨hfind, ci, hci⟩ := findRes_hit hE hC hf0
  rw [hci] at hfind
  by_cases h3 : erRd m ((findRes m vis C).tail.headD 0) ≠ 3
  · rw [ntWf.arm2 (hc1 := hf0) (hc2 := h3)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨none, a, ?_, hS, IWGrow.refl _, rfl⟩
    rw [nestContainer_none (fun cv caps e => by
      rw [hfind] at e; cases e
      have hk := decCI_indInfo_kind hci
      exact h3 (by
        have := erecP_rdN hk rfl
        exact UInt64.toNat_inj.mp (by rw [this]; rfl)))]; rfl
  rw [ntWf.arm3 (hc1 := hf0) (hc2 := Decidable.of_not_not h3)] at h
  simp only [erRd_foldN] at h
  generalize (findRes m vis C).tail.headD 0 = ciq at h hfind hci h3
  have hk3 : nat? (erecP m) ciq.toNat = some 3 := by
    obtain ⟨w, hw⟩ := decCI_rd hci
    have e := (erRd_of_erecP hw).1
    have : erRd m ciq = 3 := by simpa using h3
    simp only [nat?, hw, Option.map_some]; rw [← e, this]; rfl
  obtain ⟨cv, caps, rfl, hcaps⟩ := decCI_kind3 hci hk3
  obtain ⟨hnp, hcts⟩ := decCaps_ctors hcaps
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hcts
  obtain ⟨o, ho, l, hl, hns⟩ := hcts
  have hb : ciq.toNat + 5 + 13 + 1 < 2 ^ 64 := by obtain ⟨_, e⟩ := nat?_rd hl; exact erecP_lt64 e
  have e13 : (ciq + 5 + 13).toNat = ciq.toNat + 5 + 13 := by
    rw [L.toNat_add_of_lt _ _ (by simp; omega), L.toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have e14 : (ciq + 5 + 14).toNat = ciq.toNat + 5 + 13 + 1 := by
    rw [L.toNat_add_of_lt _ _ (by simp; omega), L.toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have e12 : (ciq + 5 + 12).toNat = ciq.toNat + 5 + 12 := by
    rw [L.toNat_add_of_lt _ _ (by simp; omega), L.toNat_add_of_lt _ _ (by simp; omega)]; rfl
  have ro := erecP_rdN ho e13
  have rl := erecP_rdN hl e14
  generalize erRd m (ciq + 5 + 13) = co at h ro
  generalize erRd m (ciq + 5 + 14) = cl at h rl
  rw [nestContainer_ind hfind]
  cases k with
  | zero => rw [ncWf.eq_1, ntWf.k_nest_container_ctors.none] at h; cases h
  | succ k =>
  rcases hnc : ncWf (k + 1) m vis C co cl with _ | ⟨r2, m2⟩ <;> rw [hnc] at h
  · rw [ntWf.k_nest_container_ctors.none] at h; cases h
  obtain ⟨ys, a', hrun, hS2, hg2, h1, h2, h3', h4⟩ := ncW_ok fe vis C hC k m m2 a co cl caps.ctors r2 hnc hS
    (by rw [ro, rl]; exact hns)
  have hrun' : (do
      let cs ← List.filterMapM (ncF fe (decI C)) caps.ctors
      match cs with
      | [] => pure (some (caps.nparams, []))
      | c :: _ => pure (some (c.2.1, cs.map fun c => (c.1, c.2.2))) : AM _).run a =
      .ok ((match ys with
        | [] => some (caps.nparams, [])
        | c :: _ => some (c.2.1, ys.map fun c => (c.1, c.2.2))), a') := by
    simp only [StateT.run_bind, hrun, except_ok_bind]; cases ys <;> rfl
  cases ys with
  | nil =>
    rw [ntWf.k_nest_container_ctors.arm1 (hc1 := by apply UInt64.toNat_inj.mp; simpa using h1)] at h
    simp only [erRd_foldN] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨_, a', hrun', hS2, hg2, rfl, ?_, rfl, by simpa using h2, by simpa using h3'⟩
    simp only [List.tail_cons, List.headD_cons]
    exact erecP_rdN ((GrowX.of_grow (q := 0) (n := 0) hg2).erecP.nat? hnp) e12
  | cons c ys =>
    rw [ntWf.k_nest_container_ctors.arm2 (hc1 := fun e => by rw [e] at h1; simp at h1)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨_, a', hrun', hS2, hg2, rfl, by simpa using h4, by simpa using h1, by simpa using h2,
      by rw [show (fun c : IConstantVal × Nat × Nat => (c.fst, c.snd.snd)) = ncProj from rfl]; simpa using h3'⟩

l_model dcGo_spec (p : Prog) (hf : HfF p) (hp : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL)
  fns [hp ↦ dcGoW list]
  specs [fvbF_spec p hf n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

l_model dc_spec' (p : Prog) (hf : HfF p) (hh : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt)
    (hg : p.lookup "nest_ds_closed_go" = some nestDsClosedGoL)
    (hp : p.lookup "nest_ds_closed" = some nestDsClosedL)
  fns [hp ↦ dcWf list]
  specs [nestCtxHiAt_specE p hh n, dcGo_spec p hf hg n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

theorem dcGoW_mfr : ∀ (n : Nat) (m m' : Mem) (hi off l : Word) (r : List Word),
    dcGoW n m hi off l = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, h => by simp [dcGoW.eq_1] at h
  | n + 1, m, m', hi, off, l, r, h => by
    simp only [dcGoW.eq_2, dcGoW.k_fvar_b.eq_def, dcGoW.k_nest_ds_closed_go.eq_def] at h
    mfr_auto h [MFr.ofFvbF, dcGoW_mfr n _ _ _ _ _ _]

theorem dcWf_mfr {n : Nat} {m m' : Mem} {ctx off l : Word} {r : List Word} (h : dcWf n m ctx off l = some (r, m')) :
    MFr [] [] m m' := by
  cases n with
  | zero => simp [dcWf.eq_1] at h
  | succ n =>
    simp only [dcWf.eq_2, dcWf.k_nest_ds_closed_go.eq_def] at h
    mfr_auto h [dcGoW_mfr _ _ _ _ _ _ _]

theorem dcGoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis hi : Word) (HI : Nat)
    (hHI : hi.toNat = HI) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (off l : Word) (ds : List EIdx) (r : List Word),
    dcGoW n m hi off l = some (r, m') → StageR vis fe m a →
    decHL m off.toNat l.toNat = some ds → (∀ j < l.toNat, off.toNat + j < iwTop m) →
    ∃ b a', (ds.allM (dsF HI)).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      r.headD 0 = (if b then 1 else 0) := by
  induction n with
  | zero => intro m m' a off l ds r h; simp [dcGoW.eq_1] at h
  | succ n ih =>
    intro m m' a off l ds r h hS hds hin
    by_cases hl0 : l = 0
    · rw [dcGoW.arm1 (hc1 := hl0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst hl0
      have : ds = [] := by simpa [decHL, hslice?] using hds.symm
      subst this
      exact ⟨true, a, rfl, hS, IWGrow.refl _, rfl⟩
    rw [dcGoW.arm2 (hc1 := hl0)] at h
    have hl : l.toNat ≠ 0 := fun e => hl0 (UInt64.toNat_inj.mp (by simpa using e))
    obtain ⟨l', hl'⟩ : ∃ l', l.toNat = l' + 1 := ⟨l.toNat - 1, by omega⟩
    have hds' := hds
    simp only [decHL, hl', hslice?_succ, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hds'
    obtain ⟨x, hx, xs, hxs, rfl⟩ := hds'
    obtain ⟨hxH, hxd⟩ := rd_iwH0E (m := m) (o := off) (k := IdxKind.expr) (by simpa [iwH, iwA, aread_apply, aread_apply] using hx)
    have hsz := hS.iw.iwSize
    have hoff1 : (off + 1).toNat = off.toNat + 1 :=
      L.toNat_add_of_lt _ _ (show off.toNat + 1 < 2 ^ 64 by have := hin 0 (by omega); have := hS.iw.iw; omega)
    have hl1 : (l - 1).toNat = l' := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    rcases hst : fvbF m [CWF, rdW (m.arr64 IW) off] with _ | ⟨r1, m1⟩ <;> rw [hst] at h; · rw [dcGoW.k_fvar_b.none] at h; cases h
    obtain ⟨k, a1, hrun1, hS1, hg1, hk⟩ := fvbF_ok dn vis fe CWF _ hxH _ _ a r1 hst hS
    rw [CWF_eq, hxd] at hrun1
    rw [List.allM_cons]
    by_cases hc : hi < r1.headD 0
    · rw [dcGoW.k_fvar_b.arm1 (hc1 := hc)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hgt : ¬ k ≤ HI := by
        have := UInt64.lt_iff_toNat_lt.mp hc; simp only [decW0Nat] at hk; omega
      refine ⟨false, a1, ?_, hS1, hg1, rfl⟩
      simp only [dsF, StateT.run_bind, hrun1, except_ok_bind, hgt, decide_false]
      rfl
    · rw [dcGoW.k_fvar_b.arm2 (hc1 := hc)] at h
      rcases hgo : dcGoW n m1 hi (off + 1) (l - 1) with _ | ⟨r', m''⟩ <;> rw [hgo] at h
      · rw [dcGoW.k_nest_ds_closed_go.none] at h; cases h
      rw [dcGoW.k_nest_ds_closed_go.arm1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hle : k ≤ HI := by
        have : ¬ hi.toNat < (r1.headD 0).toNat := fun e => hc (UInt64.lt_iff_toNat_lt.mpr e)
        simp only [decW0Nat] at hk; omega
      have hRd : RdS m m1 (· < iwTop m) := RdS.of_grow hg1
      obtain ⟨b, a', hrun, hS', hg', hr⟩ := ih m1 m'' a1 (off + 1) (l - 1) xs r' hgo hS1
        (by rw [hoff1, hl1, ← hxs, decHL]; exact decHL_agree hRd (fun j hj => by
              have := hin (j + 1) (by omega); simp only [decHL] at *; omega))
        (fun j hj => by rw [hoff1, hl1] at *; have := hin (j + 1) (by omega); have := hg1.iw; omega)
      refine ⟨b, a', ?_, hS', hg1.trans hg', hr⟩
      simp only [dsF, StateT.run_bind, hrun1, except_ok_bind, hle, decide_true]
      exact hrun

/-- `nest_ds_closed` from the stage relation: `ds.allM (fvarB · ≤ ctx.hiAt 0)`. -/
theorem dcWf_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) (m m' : Mem)
    (a : AState) (ctx off l : Word) (c : NestCtx) (ds : List EIdx) (r : List Word)
    (h : dcWf n m ctx off l = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hhi : c.hiAt 0 < 2 ^ 64) (hds : decHL m off.toNat l.toNat = some ds)
    (hdi : ∀ j < l.toNat, off.toNat + j < iwTop m) :
    ∃ b a', (ds.allM (dsF (c.hiAt 0))).run a = .ok (b, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      r.headD 0 = (if b then 1 else 0) := by
  cases n with
  | zero => simp [dcWf.eq_1] at h
  | succ n =>
    have hsz : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.iw.iw hS.iw.iwSize
    rw [dcWf.arm1] at h
    rcases hgo : dcGoW n m (nhiW m ctx 0) off l with _ | ⟨r', m''⟩ <;> rw [hgo] at h
    · rw [dcWf.k_nest_ds_closed_go.none] at h; cases h
    rw [dcWf.k_nest_ds_closed_go.arm1] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact dcGoW_ok dn fe vis _ _ (by simpa using nhiW_toNat (nf := 0) hc hin hsz (by simpa using hhi)) n
      m _ a off l ds r' hgo hS hds hdi

/-! ## `nest_walk_stack` refines `nestWalkStack` -/

l_model nestWalkStack_spec (p : Prog) (hl : DcLook p)
    (hp : p.lookup "nest_walk_stack" = some nestWalkStackL)
  fns [hp ↦ nwsWf list]
  specs [dc_spec' p hl.hf hl.hh hl.hg hl.hp n]
  grind [arena_grind] fold [tierW, idxW] finish [tierW, idxW]

theorem nestWalkStack_eq (ctx : NestCtx) (prog : List NestHole) (ds : List EIdx) :
    ConRon.Arena.nestWalkStack ctx prog ds = (do
      let closed ← ds.allM (dsF (ctx.hiAt 0))
      if closed then pure [] else pure prog) := rfl

theorem nwsW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis : Word) (n : Nat) (m m' : Mem)
    (a : AState) (ctx off l po pl : Word) (c : NestCtx) (ds : List EIdx) (prog : List NestHole)
    (r : List Word) (h : nwsWf (n + 1) m ctx off l po pl = some (r, m')) (hS : StageR vis fe m a)
    (hc : decCtx m ctx.toNat = some c) (hin : CtxIn m ctx.toNat (· < iwTop m))
    (hhi : c.hiAt 0 < 2 ^ 64) (hds : decHL m off.toNat l.toNat = some ds)
    (hdi : ∀ j < l.toNat, off.toNat + j < iwTop m) :
    ∃ x a', (ConRon.Arena.nestWalkStack c prog ds).run a = .ok (x, a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ ((x = [] ∧ r = [0, 0]) ∨ (x = prog ∧ r = [po, pl])) := by
  rw [nwsWf.arm1] at h
  rcases hd : dcWf n m ctx off l with _ | ⟨r1, m1⟩ <;> rw [hd] at h; · rw [nwsWf.k_nest_ds_closed.none] at h; cases h
  obtain ⟨b, a', hrun, hS', hg, hr⟩ := dcWf_ok dn fe vis n m m1 a ctx off l c ds r1 hd hS hc hin hhi hds hdi
  rw [nestWalkStack_eq]
  cases b with
  | true =>
    rw [nwsWf.k_nest_ds_closed.arm1 (hc1 := by rw [hr]; decide)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨[], a', ?_, hS', hg, Or.inl ⟨rfl, rfl⟩⟩
    simp only [StateT.run_bind, hrun, except_ok_bind]; rfl
  | false =>
    rw [nwsWf.k_nest_ds_closed.arm2 (hc1 := by rw [hr]; decide)] at h
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
    (hS : StageR vis fe s₀.mem a₀) (hc : decCtx s₀.mem ctx.toNat = some c)
    (hin : CtxIn s₀.mem ctx.toNat (· < iwTop s₀.mem)) (hhi : c.hiAt 0 < 2 ^ 64)
    (hds : decHL s₀.mem off.toNat l.toNat = some ds) (hdi : ∀ j < l.toNat, off.toNat + j < iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "nest_walk_stack" [ctx, off, l, po, pl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.nestWalkStack c prog ds) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.nestWalkStack c prog ds) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      ((AM.res (ConRon.Arena.nestWalkStack c prog ds) a₀ = [] ∧ r = [0, 0]) ∨
        (AM.res (ConRon.Arena.nestWalkStack c prog ds) a₀ = prog ∧ r = [po, pl])); ⊤⦄ := by
  refine triple_post (nestWalkStack_spec p hl hp (n + 1) s₀ ctx off l po pl) ?_
  rintro r s' ⟨hlc, hm⟩
  obtain ⟨x, a', hrun, hS', hg, hout⟩ := nwsW_ok dn fe vis n _ _ a₀ ctx off l po pl c ds prog r hm hS hc
    hin hhi hds hdi
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlc, hok, by rw [hst]; exact hS', hg, by rw [hres]; exact hout⟩

end census

theorem pdoW_ok (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis no nl lo hi : Word)
    (names : List NIdx) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (n e : Word) (r : List Word) (mp : Std.HashMap EIdx Bool),
    pdoW k m no nl lo hi n e = some (r, m') → StageR vis fe m a → H e →
    decHL m no.toNat nl.toNat = some names → (∀ j < nl.toNat, no.toNat + j < iwTop m) →
    noMR m mp →
    ∃ b a' mp', (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ r.headD 0 = (if b then 1 else 0) ∧ noMR m' mp' ∧
      MFr [NOM] [204, 205] m m' := by
  induction k with
  | zero => intro m m' a n e r mp h; simp [pdoW.eq_1] at h
  | succ k ih =>
    intro m m' a n e r mp h hS he hn hnb hM
    by_cases h0 : n = 0
    · rw [pdoW.arm1 (hc1 := h0)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      subst h0
      exact ⟨false, a, mp, rfl, hS, IWGrow.refl _, rfl, hM, MFr.refl _ _ _⟩
    have hn0 : n.toNat ≠ 0 := fun e' => h0 (UInt64.toNat_inj.mp (by simpa using e'))
    have hsucc : n.toNat = (n.toNat - 1) + 1 := by omega
    by_cases h6 : tagW e ≠ 6
    · rw [pdoW.arm2 (hc1 := h0) (hc2 := h6)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      refine ⟨false, a, mp, ?_, hS, IWGrow.refl _, rfl, hM, MFr.refl _ _ _⟩
      have htag : ¬ (decE e).tag = ETag.forallE := fun h' => h6 ((decE_tag_forallE e he).mp h')
      rw [hsucc, ConRon.Arena.piDomsOcc.eq_2]
      simp [htag]; rfl
    have hg6 : tagW e = 6 := by simpa using h6
    have hR := hS.check.arena.base
    by_cases hr : eViewW m e = []
    · rw [pdoW.abort1 (hc1 := h0) (hc2 := hg6) (hc3 := hr)] at h; cases h
    rw [pdoW.arm3 (hc1 := h0) (hc2 := hg6) (hc3 := hr)] at h
    obtain ⟨hvok, hew⟩ := eViewW_forall m e hg6 hr
    obtain ⟨-, hty, hb⟩ := view_forall m a hR e he hvok hg6
    have hvb := viewBind_forall m a hR e he hvok hg6
    simp only [hew, List.tail_cons, List.headD_cons] at h
    generalize hd : tfld m FORALL (tierW e) (idxW e) 0 = d at h hty hvb
    generalize hbd : tfld m FORALL (tierW e) (idxW e) 1 = b at h hb hvb
    rcases hnc : noConstWf k m no nl lo hi d with _ | ⟨r1, m1⟩ <;> rw [hnc] at h; · rw [pdoW.k_nest_occ.none] at h; cases h
    have hnb' : no.toNat + nl.toNat < 2 ^ 64 := by
      rcases Nat.eq_zero_or_pos nl.toNat with hz | hz
      · rw [hz]; simpa using no.toNat_lt
      · have := hnb (nl.toNat - 1) (by omega); have := hS.iw.iw; have := hS.iw.iwSize; omega
    obtain ⟨c, hrun1, hc, hM1, hS1, hg1, hf1⟩ := noConstWf_ok k dn fe vis m m1 a no nl lo hi d r1 names mp hnc
      hS hty hn hnb' hM
    have hpre : (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)).run a =
        (do let x ← ConRon.Arena.nestOcc names lo.toNat hi.toNat (decE d)
            if x = true then pure true
            else ConRon.Arena.piDomsOcc names lo.toNat hi.toNat (n.toNat - 1) (decE b)).run a := by
      rw [hsucc, ConRon.Arena.piDomsOcc.eq_2]
      have htag : (decE e).tag = ETag.forallE := (decE_tag_forallE e he).mpr hg6
      simp only [htag, beq_self_eq_true, ite_true, StateT.run_bind, L.Arena.viewBind_run _ a, hvb, except_ok_bind]
      rfl
    by_cases hr1 : r1 ≠ 0
    · rw [pdoW.k_nest_occ.arm1 (hc1 := hr1)] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hcT : c = true := by rw [← hc]; simpa using hr1
      subst hcT
      refine ⟨true, a, ∅, ?_, hS1, hg1, rfl, hM1, hf1⟩
      rw [hpre]; simp only [StateT.run_bind, hrun1, except_ok_bind]; rfl
    · rw [pdoW.k_nest_occ.arm2 (hc1 := by simpa using hr1)] at h
      have hcF : c = false := by rw [← hc]; simpa using hr1
      subst hcF
      have hn1 : (n - 1).toNat = n.toNat - 1 :=
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))
      rcases hrec : pdoW k m1 no nl lo hi (n - 1) b with _ | ⟨r', m''⟩ <;> rw [hrec] at h
      · rw [pdoW.k_pi_doms_occ.none] at h; cases h
      rw [pdoW.k_pi_doms_occ.arm1] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨b', a', mp', hrun, hS', hg', hr', hM', hf'⟩ := ih m1 m'' a (n - 1) b r' ∅ hrec hS1 hb
        (by rw [decHL_agree (RdS.of_grow hg1) hnb]; exact hn)
        (fun j hj => Nat.lt_of_lt_of_le (hnb j hj) hg1.iw) hM1
      refine ⟨b', a', mp', ?_, hS', hg1.trans hg', by simpa using hr', hM', hf1.trans hf'⟩
      rw [hpre]; simp only [StateT.run_bind, hrun1, except_ok_bind]
      rw [← hn1]; exact hrun

section census
variable (p : Prog) (hl : NoLook p) (hp : p.lookup "pi_doms_occ" = some piDomsOccL)
include hl hp

/-- **`pi_doms_occ` refines `piDomsOcc`** (the `nest_occ` memo well-formed on entry). -/
@[refines ConRon.Arena.piDomsOcc]
theorem piDomsOcc_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (fe : IFEnv) (vis no nl lo hi n e : Word) (names : List NIdx) (mp : Std.HashMap EIdx Bool)
    (hS : StageR vis fe s₀.mem a₀) (he : H e) (hn : decHL s₀.mem no.toNat nl.toNat = some names)
    (hnb : ∀ j < nl.toNat, no.toNat + j < iwTop s₀.mem) (hM : noMR s₀.mem mp) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "pi_doms_occ" [no, nl, lo, hi, n, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)) a₀ ∧
      StageR vis fe s'.mem (AM.st (ConRon.Arena.piDomsOcc names lo.toNat hi.toNat n.toNat (decE e)) a₀) ∧
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

theorem CNOk.grow {m m' : Mem} {p : Nat} {x : IConstantVal × Nat} (h : CNOk m p x (· < iwTop m))
    (hg : IWGrow m m') : CNOk m' p x (· < iwTop m') :=
  (h.agree (RdS.of_grow hg) (GrowX.of_grow (q := 0) (n := 0) hg).erecP).mono
    fun _ hx => Nat.lt_of_lt_of_le hx hg.iw

end L.Ind

end
