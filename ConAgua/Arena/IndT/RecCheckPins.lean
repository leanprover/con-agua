import ConAgua.Arena.RecCheckSpec5
import ConAgua.Arena.IndT.Lift
import ConRon.Bridge.Inductives.RecCheck
import ConAgua.Arena.RecClassSpecH
import ConAgua.Arena.RecGenSpec5

/-!
# `targetPinTys`, `targetMajorPins` under `StageC` (lane `indstaget`, helper `indstaget-tpt`)

`target_pin_tys`' and `target_major_pins`' models at `realCall p`, from `StageC`, `AbsOK` and the
inputs' denotations con-ron's `targetPinTys_spec`/`targetMajorPins_spec` ask (the parameters'
denotations and their scoping at the rule prefix), the twin side transcribed from those specs'
proofs: `inferTypeCore` (`inferC_rsim`), the head's intern (`internConstE_run`), `mkAppN`
(`mkAppN_run`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)

include hq henv in
/-- **`target_pin_tys` under `StageC`** (twin side: con-ron's `targetPinTys_spec`'s proof). -/
theorem tptW_okC (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m m' : Mem) (a : AState) (d xo xl : Word) (r : List Word) (xs : List EIdx)
      (xsP : List ConLeche.Expr),
    tptW (realCall p) n m vis d xo xl = some (r, m') → StageC dn vis fe env m a → AbsOK m →
    decHL m xo.toNat xl.toNat = some xs → xo.toNat + xl.toNat < 2 ^ 64 →
    xo.toNat + xl.toNat ≤ iwTop m → Frontend.denoteEList a.store xs = some xsP →
    (∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) →
    ∃ a', (ConRon.Arena.targetPinTys V fe d.toNat xs).run a = .ok ((), a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a d xo xl r xs xsP h; simp [tptW] at h
  | succ n ih =>
    intro m m' a d xo xl r xs xsP h hC hA hxs hb hbt hxsP hw
    by_cases hxl : xl = 0
    · rw [tptW_nil (realCall p) n m vis d xo xl hxl] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have hz : xl.toNat = 0 := by rw [hxl]; rfl
      rw [hz] at hxs
      simp [decHL, hslice?] at hxs
      subst hxs
      exact ⟨a, rfl, hC, IWGrow.refl m, hA⟩
    · rw [tptW_cons (realCall p) n m vis d xo xl hxl] at h
      have hpos : 1 ≤ xl.toNat := by
        rcases Nat.eq_zero_or_pos xl.toNat with h0 | h0
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hxl
        · omega
      obtain ⟨c1, hc1⟩ : ∃ c1, xl.toNat = c1 + 1 := ⟨xl.toNat - 1, by omega⟩
      rw [hc1] at hxs
      obtain ⟨x, xs', rfl, hxs', hx⟩ := decHL_cons_r hxs
      obtain ⟨w, hw1, hw2, hw3⟩ := iwH_rdW hx (by omega)
      rw [UInt64.ofNat_toNat] at hw1
      have hxl1 : (xl - 1).toNat = c1 := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using hpos))]; simp; omega
      have hxo1 : (xo + 1).toNat = xo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      rw [hw1] at h
      obtain ⟨xP, xsP', hxP, hxsP', rfl⟩ := ConRon.Bridge.denoteEList_cons_inv hxsP
      cases hi : realCall p n "infer_type_core" [vis, d, w] m with
      | none => rw [hi] at h; simp [tptK] at h
      | some rm =>
        obtain ⟨ri, m1⟩ := rm
        rw [hi, tptK_some (realCall p)] at h
        rw [← hw3] at hxP
        obtain ⟨t1, a1, hrun1, hC1, hg1, -, hA1, c1', -⟩ :=
          inferC_rsim hq henv n (by omega) hC hA d w hw2 hxP (hw xP List.mem_cons_self) _ hi
        dsimp only at hC1 hg1 hA1
        rcases hr : tptW (realCall p) n m1 vis d (xo + 1) (xl - 1) with _ | ⟨r2, m2⟩ <;> simp only [hr, tptK2, reduceCtorEq] at h
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        have hxs1 : decHL m1 (xo + 1).toNat (xl - 1).toNat = some xs' := by
          rw [hxo1, hxl1, decHL_grow hg1 (by omega)]; exact hxs'
        obtain ⟨a2, hrun2, hC2, hg2, hA2⟩ := ih (by omega) m1 m2 a1 d (xo + 1) (xl - 1) r2 xs' xsP'
          hr hC1 hA1 hxs1 (by rw [hxo1, hxl1]; omega) (by rw [hxo1, hxl1]; have := hg1.1; omega)
          (ConRon.Bridge.denoteEList_ext c1'.ext _ _ hxsP')
          (fun y hy => hw y (List.mem_cons_of_mem _ hy))
        refine ⟨a2, ?_, hC2, hg1.trans hg2, hA2⟩
        rw [ConRon.Arena.targetPinTys, StateT.run_bind, ← hw3, hrun1]
        exact hrun2

include hq henv in
/-- **`target_pin_tys` refines `targetPinTys .verified`** under `StageC` (the knot's
`infer_type_core`; the parameters' denotations and scoping as con-ron's `targetPinTys_spec`
asks). -/
@[refines ConRon.Arena.targetPinTys]
theorem targetPinTys_refinesC (hp : p.lookup "target_pin_tys" = some targetPinTys) (n : Nat)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (d xo xl : Word) (xs : List EIdx)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hxs : decHL s₀.mem xo.toNat xl.toNat = some xs) (hb : xo.toNat + xl.toNat < 2 ^ 64)
    (hbt : xo.toNat + xl.toNat ≤ iwTop s₀.mem) {xsP : List ConLeche.Expr}
    (hxsP : Frontend.denoteEList a₀.store xs = some xsP)
    (hw : ∀ x ∈ xsP, ConLeche.Expr.WScoped d.toNat x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "target_pin_tys" [vis, d, xo, xl]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.targetPinTys V fe d.toNat xs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (targetPinTys_spec p hp (realCall p) (realCall_spec p) n s₀ vis d xo xl) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hC', hg, hA'⟩ :=
    tptW_okC hq henv n hn _ _ a₀ d xo xl _ xs xsP hm hC hA hxs hb hbt hxsP hw
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ a₀ a' () hrun
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, hA'⟩

include hq henv in
/-- **`target_major_pins` under `StageC`** (twin side: con-ron's `targetMajorPins_spec`'s proof):
`tptW_okC`, the head's intern (`internConstE_run`), `mkAppN` (`mkAppN_run`), `inferC_rsim`. -/
theorem tmpW_okC {a : AState} {N : Nat} (hN : N ≤ 2 ^ 62) {m m' : Mem} {rP Mp : Word}
    {r : List Word} {M : TargetMajor} (h : tmpW (realCall p) N m vis rP Mp = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hM : DecB (fun m => decTM m Mp.toNat) m M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    ∃ a', (ConRon.Arena.targetMajorPins V fe rP.toNat M).run a = .ok ((), a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  obtain _ | N := N
  · simp [tmpW] at h
  have hS := hC.stage
  have hsz := hS.2.2.2.1
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨k, hk, hmem⟩ := decTM_member hM0
  obtain ⟨hind, hlv, hdsd, -, -, -, hmemP, -, -⟩ := ConRon.Bridge.Inductives.dMajor_inv hMP
  have hrk := iwN_rdW_at (w := Mp) (k := 8) hk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  by_cases hk0 : rdW (m.arr64 IW) (Mp + 8) ≠ 0
  · rw [tmpW_mem (h := hk0)] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have hk0' : k ≠ 0 := by intro e; apply hk0; rw [hrk.1, e]; rfl
    have hmem' : M.member = some (k - 1) := by rw [hmem]; simp [decON, hk0']
    exact ⟨a, by simp [ConRon.Arena.targetMajorPins, hmem']; rfl, hC, IWGrow.refl m, hA⟩
  rw [tmpW_out (h := hk0)] at h
  have hk00 : k = 0 := by
    have : rdW (m.arr64 IW) (Mp + 8) = 0 := by simpa using hk0
    rw [hrk.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' hrk.2] at this
  have hmem' : M.member = none := by rw [hmem, hk00]; rfl
  have hw := hds (by rw [← hmemP, hmem'])
  obtain ⟨o, l, hoT, hlT, hdT⟩ := decTM_ds (show decTM (truncM m) Mp.toNat = some M from hM)
  obtain ⟨hoi, ho⟩ := iwN_truncM_get hoT
  obtain ⟨hli, hl⟩ := iwN_truncM_get hlT
  have hdsm : decHL m o l = some M.ds := (OMono.decHL o l).mono _ _ _ (IWGrow.refl m).truncExt hdT
  have ro := iwN_rdW_at (w := Mp) (k := 2) ho hsz
  have rl := iwN_rdW_at (w := Mp) (k := 3) hl hsz
  rw [show UInt64.ofNat 2 = (2 : Word) from rfl] at ro
  rw [show UInt64.ofNat 3 = (3 : Word) from rfl] at rl
  rw [ro.1, rl.1] at h
  have hoo := UInt64.toNat_ofNat_of_lt' ro.2
  have hll := UInt64.toNat_ofNat_of_lt' rl.2
  -- the pins of the parameters
  obtain ⟨a1, m1, r1, h1, hrun1, hC1, hg1, hA1⟩ : ∃ a1 m1 r1,
      tptW (realCall p) N m vis rP (UInt64.ofNat o) (UInt64.ofNat l) = some (r1, m1) ∧
      (ConRon.Arena.targetPinTys V fe rP.toNat M.ds).run a = .ok ((), a1) ∧
      StageC dn vis fe env m1 a1 ∧ IWGrow m m1 ∧ AbsOK m1 := by
    cases h1 : tptW (realCall p) N m vis rP (UInt64.ofNat o) (UInt64.ofNat l) with
    | none => rw [h1] at h; simp [tmpK1] at h
    | some rm1 =>
    obtain ⟨r1, m1⟩ := rm1
    by_cases hl0 : l = 0
    · subst hl0
      have hnil : M.ds = [] := by simpa [decHL, hslice?] using hdsm.symm
      obtain _ | N := N
      · simp [tptW] at h1
      rw [tptW_nil (realCall p) N m vis rP (UInt64.ofNat o) (UInt64.ofNat 0) rfl] at h1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h1)
      exact ⟨a, m, [], rfl, by rw [hnil]; rfl, hC, IWGrow.refl m, hA⟩
    have hbnd := decHL_truncM_bound hdT hl0
    obtain ⟨a1, hrun1, hC1, hg1, hA1⟩ := tptW_okC hq henv N (by omega) m m1 a rP _ _ r1 M.ds MP.ds
      h1 hC hA (by rw [hoo, hll]; exact hdsm) (by rw [hoo, hll]; have := hS.2.1; omega)
      (by rw [hoo, hll]; exact hbnd) hdsd hw
    exact ⟨a1, m1, r1, rfl, hrun1, hC1, hg1, hA1⟩
  obtain ⟨c1, -⟩ := ConRon.Bridge.Inductives.targetPinTys_spec fe (ConRon.Bridge.CoreSpec.of_core rfl)
    henv rP.toNat M.ds MP.ds hw a a1 () hC.check hdsd hrun1
  rw [h1, tmpK1_some] at h
  have hS1 := hC1.stage
  have hM1 : decTM m1 Mp.toNat = some M := hM.stab (decTM_mono _) m1 hg1
  obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := Mp) (k := 0) (by simpa using decTM_ind hM1) hS1.2.2.2.1
  obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := Mp) (k := 1) (decTM_lvls' hM1) hS1.2.2.2.1
  rw [show Mp + UInt64.ofNat 0 = Mp by simp] at hwi
  rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
  rw [hwi, hwu] at h
  rcases h2 : ceinternW m1 wi wu with _ | ⟨hd, m2⟩ <;> simp only [h2, tmpK2, reduceCtorEq] at h
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 wi wu hwiH hwuH h2
  rw [hwiE, hwuE] at hrun2
  obtain ⟨p2, hhd⟩ := ConRon.Bridge.Inductives.internConstE_run c1.ok.state
    (ConRon.Bridge.denoteN_ext hind c1.ext) (ConRon.Bridge.denoteLs_ext hlv c1.ext) hrun2
  have hA2 := ceinternW_afr h2 hA1
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hS2 hA2 p2
  have c2 := c1.trans (p2.toCore c1.ok)
  by_cases hbig : 4294967296 ≤ hd
  · rw [ite_eq_left hbig] at h; cases h
  rw [ite_eq_right hbig] at h
  have hdH : H hd := by
    have : ¬ (4294967296 : Word).toNat ≤ hd.toNat := fun x => hbig (UInt64.le_iff_toNat_le.mpr x)
    simp at this; exact this
  have hg12 := hg1.trans hg2
  have hts : iwTop m ≤ (m.arr64 IW).size := hS.2.1
  have e2 : rdW (m2.arr64 IW) (Mp + 2) = UInt64.ofNat o := by
    rw [← ro.1]; simp only [rdW]
    rw [show (Mp + 2).toNat = Mp.toNat + 2 by rw [UInt64.toNat_add]; simp; omega, hg12.2.2.1 _ hoi]
  have e3 : rdW (m2.arr64 IW) (Mp + 3) = UInt64.ofNat l := by
    rw [← rl.1]; simp only [rdW]
    rw [show (Mp + 3).toNat = Mp.toNat + 3 by rw [UInt64.toNat_add]; simp; omega, hg12.2.2.1 _ hli]
  rw [e2, e3] at h
  rcases h3 : mknF m2 [hd, UInt64.ofNat o, UInt64.ofNat l] with _ | ⟨r3, m3⟩ <;> simp only [h3, tmpK3, reduceCtorEq] at h
  have hds2 : decHL m2 (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat = some M.ds := by
    rw [hoo, hll]; exact (OMono.decHL o l).mono _ _ _ hg12.truncExt hdT
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := mknF_ok dn vis fe hd _ _ hdH M.ds m2 m3 a2 r3 h3 ⟨hS2, hds2⟩
  have hrun3' : (ConRon.Arena.mkAppN (decE hd) M.ds) a2 = .ok (x3, a3) := hrun3
  obtain ⟨p3, happ⟩ := ConRon.Bridge.Inductives.mkAppN_run M.ds MP.ds c2.ok.state hhd
    (ConRon.Bridge.denoteEList_ext c2.ext _ _ hdsd) hrun3'
  have hrun3r : (ConRon.Arena.mkAppN (decE hd) M.ds).run a2 = .ok (x3, a3) := hrun3
  have hA3 := mknF_afr h3 hA2
  have hC3 : StageC dn vis fe env m3 a3 := hC2.of_pstep hS3 hA3 p3
  rcases h4 : realCall p N "infer_type_core" [vis, rP, r3.headD 0] m3 with _ | ⟨r4, m4⟩ <;> simp only [h4, tmpK4, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  rw [← hx3.2] at happ
  obtain ⟨x4, a4, hrun4, hC4, hg4, -, hA4, -⟩ := inferC_rsim hq henv N (by omega) hC3 hA3 rP
    (r3.headD 0) hx3.1 happ
    (ConLeche.Expr.WScoped.mkAppN (by simp [ConLeche.Expr.WScoped]) hw) _ h4
  dsimp only at hC4 hg4 hA4
  rw [hx3.2] at hrun4
  refine ⟨a4, ?_, hC4, (hg12.trans hg3).trans hg4, hA4⟩
  simp only [ConRon.Arena.targetMajorPins, hmem', StateT.run_bind, hrun1, exc_ok_bind',
    internConstE, hrun2, hrun3r, hrun4]
  rfl

include hq henv in
/-- **`target_major_pins` refines `targetMajorPins`** under `StageC` (the knot's
`infer_type_core`; the major's denotation and its parameters' scoping as con-ron's
`targetMajorPins_spec` asks). -/
@[refines ConRon.Arena.targetMajorPins]
theorem targetMajorPins_refinesC (hp : TmpProg p) (N : Nat) (hN : N ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (rP Mp : Word) (M : TargetMajor) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hM : DecB (fun m => decTM m Mp.toNat) s₀.mem M)
    {MP : ConLeche.TargetMajor} (hMP : dMajor a₀.store M = some MP)
    (hds : MP.member = none → ∀ x ∈ MP.ds, ConLeche.Expr.WScoped rP.toNat x) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, Mp]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (targetMajorPins_spec p hp (realCall p) (realCall_spec p) N s₀ vis rP Mp) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hC', hg, hA'⟩ := tmpW_okC hq henv hN hm hC hA hM hMP hds
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hC', hg, hA'⟩

end sims

end L.Ind
