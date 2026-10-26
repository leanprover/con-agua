import ConAgua.Arena.IndInstallSpec14

/-!
# Refinements of `IndInstall`, part 15 (lane `indproofs2`, helper `install`): `checkBlockInds`

The formers' constants `cvTa₀ :: cvs.map (·.1)` (`check_block_inds_cv_tas`, `sl_cons`-built,
D18), `block_shape_with_sort` below the tops, then stage 1: the formers checked, agreed, consed.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_inds_cv_tas` -/

/-- **`check_block_inds_cv_tas_go` is its model `icvgW`** (generated). -/
l_model icvg_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
  fns [hp ↦ icvgW]
  specs [callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- **`check_block_inds_cv_tas` is its model `icvW`** (generated). -/
l_model icv_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas)
  fns [hp ↦ icvW]
  specs [callW_spec p n "check_block_inds_cv_tas_go", callW_spec p n "sl_cons"]
  grind [ind_grind] finish [rdW_eq] gen 20

/-- `sl_cons`' run under the stage relation. -/
theorem installConsRun {p : Prog} (hP : CstProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hxs : PSlR f xs o l m) (hy : DecB (fun m => f m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ x o l) h
  obtain ⟨hS', hg, hd, htop⟩ := partsConsPL hf hW hS hxs.2 hxs.1 hy
  exact ⟨hS', hg, hd, Nat.le_of_eq htop⟩

/-- **`check_block_inds_cv_tas_go`'s model**: the constants of the `[cvTa, s]` records. -/
theorem icvgW_ok {p : Prog} (hP : CstProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) : ∀ (m m' : Mem) (s l : Word) (r : List Word)
      (xs : List (IConstantVal × LIdx)),
    icvgW p n m s l = some (r, m') → StageR dn vis fe m a → PSlR decTele xs s l m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PSlR decCVp (xs.map (·.1)) (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' s l r xs h; rw [icvgW.eq_1] at h; cases h
  | succ n ih =>
  intro m m' s l r xs h hS hxs
  by_cases hl : l = 0
  · rw [icvgW.arm1 p n m s l hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : xs = [] := by
      have h := hxs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨hS, IWGrow.refl m, PSlR.nil decCVp m⟩
  obtain ⟨q, x, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hxs hl
  rw [icvgW.arm2 p n m s l hl] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h (icvgW.k_check_block_inds_cv_tas_go.none ..)
  rw [icvgW.k_check_block_inds_cv_tas_go.arm1] at h
  obtain ⟨hS1, hg1, hd1⟩ := ih m m1 (s + 1) (l - 1) r1 rest h1 hS hrest
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [icvgW.k_sl_cons.arm1] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  -- the record's first word
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hsl : s.toNat < iwTop m := by have := hxs.2; omega
  have hw1 : rdW (m1.arr64 IW) s = UInt64.ofNat q := by rw [← hw]; simp only [rdW]; rw [hg1.2.2.1 _ hsl]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hdx' : decTele (truncM m) q = some x := hdx
  simp only [decTele, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdx'
  obtain ⟨c, hc, cv, hcv, sv, -, rfl⟩ := hdx'
  obtain ⟨hwc, hcb, hclt⟩ := partsIwRd hc (w := UInt64.ofNat q) hq'
  have hqlt : q < iwTop m := partsIwLt hc
  have hwc1 : rdW (m1.arr64 IW) (UInt64.ofNat q) = UInt64.ofNat c := by
    rw [← hwc]; simp only [rdW, hq']; rw [hg1.2.2.1 _ hqlt]
  rw [hw1, hwc1] at h2
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  obtain ⟨hS2, hg2, hd2⟩ := installConsRun hP (fun q => OMono.decCVp q) h2 hS1 hd1
    (by rw [hc']; exact (show DecB (fun m => decCVp m c) m cv from hcv).grow (OMono.decCVp _) hg1)
  exact ⟨hS2, hg1.trans hg2, by simpa using hd2⟩

/-- `check_block_inds_cv_tas`' run: `c0 :: cvs.map (·.1)`, a slice of constants below the tops. -/
theorem installCvTasRun {p : Prog} (hP : CstProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem} {c0 o l : Word} {r : List Word}
    {cv0 : IConstantVal} {cvs : List (IConstantVal × LIdx)}
    (hcv : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas)
    (hcg : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
    (h : callW p n "check_block_inds_cv_tas" [c0, o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hc0 : DecB (fun m => decCVp m c0.toNat) m cv0) (hcvs : PSlR decTele cvs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decCVp (cv0 :: cvs.map (·.1)) (r.headD 0) (r.tail.headD 0) m' := by
  rcases n with _ | n
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (icv_spec p hcv (n + 1) _ c0 o l) h
  rw [icvW.arm1] at hW
  obtain ⟨⟨r1, m1⟩, h1, hW⟩ := of_K hW rfl
  rw [icvW.k_check_block_inds_cv_tas_go.arm1] at hW
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (icvg_spec p hcg n _ o l) h1
  obtain ⟨hS1, hg1, hd1⟩ := icvgW_ok hP n _ _ o l r1 cvs hW1 hS hcvs
  obtain ⟨⟨r2, m2⟩, h2, hW⟩ := of_K hW rfl; rw [icvW.k_sl_cons.arm1] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hS2, hg2, hd2⟩ := installConsRun hP (fun q => OMono.decCVp q) h2 hS1 hd1
    (hc0.grow (OMono.decCVp _) hg1)
  exact ⟨hS2, hg1.trans hg2, by simpa using hd2⟩

/-- The recursor shapes' slice of the shape at `pp` lies below the top. -/
def RecsB (m : Mem) (pp : Word) : Prop :=
  ∀ o l, iwN m (pp.toNat + 2) = some o → iwN m (pp.toNat + 3) = some l → o + l ≤ iwTop m

theorem RecsB.grow {m m' : Mem} {pp : Word} (h : RecsB m pp) (hg : IWGrow m m') (h3 : pp.toNat + 3 < iwTop m) :
    RecsB m' pp := by
  intro o l ho hl
  rw [iwN_grow hg (by omega)] at ho
  rw [iwN_grow hg h3] at hl
  exact Nat.le_trans (h o l ho hl) hg.1

/-- Every member's former constant record lies below the tops (`CVExt`). -/
def ShapeCV (m : Mem) (q : Word) : Prop :=
  ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → ∀ j < l, ∀ c,
    iwN m (o + j) = some c → ∀ d, iwN m c = some d → CVExt m d

/-! ## `check_block_inds` -/

/-- **`check_block_inds` is its model `ibiW`** (generated). -/
l_model ibi_spec (p : Prog) (hp : p.lookup "check_block_inds" = some checkBlockInds)
  fns [hp ↦ ibiW]
  specs [callW_spec p n "check_block_tele", callW_spec p n "check_block_teles",
    callW_spec p n "check_block_agree", callW_spec p n "block_shape_with_sort",
    callW_spec p n "check_block_inds_cv_tas", callW_spec p n "cons_block_inds"]
  grind [ind_grind] finish [rdW_eq] gen 40 heartbeats 1600000 instances 20000

end L.Ind
