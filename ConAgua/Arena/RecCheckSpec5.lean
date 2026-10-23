import ConAgua.Arena.RecGenSpec5
import ConAgua.Arena.ConstStore

/-!
# More refinements of `RecCheck` (lane `indproofs2`, helper `rec`): `targetMajorPins`
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_major_pins` -/

def tmpK4 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m4) => some ([], m4)

def tmpK3 (vis rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) => tmpK4 (stubM "infer_type_core" m3 [vis, rP, r3.headD 0])

def tmpK2 (vis rP M : Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (hd, m2) =>
    if 4294967296 ≤ hd then none
    else tmpK3 vis rP (mknF m2
      [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)])

def tmpK1 (vis rP M : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m1) => tmpK2 vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1)))

/-- **The model of `target_major_pins`.** -/
def tmpW : Nat → Mem → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _ => none
  | N + 1, m, vis, rP, M =>
    if rdW (m.arr64 IW) (M + 8) ≠ 0 then some ([], m)
    else tmpK1 vis rP M (tptW N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3)))

section arms
variable (N : Nat) (m m1 m2 m3 m4 : Mem) (vis rP M hd : Word) (r1 r3 r4 : List Word)
theorem tmpW_mem (h : rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW (N + 1) m vis rP M = some ([], m) := by
  simp only [tmpW]; rw [if_pos h]
theorem tmpW_out (h : ¬ rdW (m.arr64 IW) (M + 8) ≠ 0) : tmpW (N + 1) m vis rP M =
    tmpK1 vis rP M (tptW N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3))) := by
  simp only [tmpW]; rw [if_neg h]
theorem tmpK1_some : tmpK1 vis rP M (some (r1, m1)) =
    tmpK2 vis rP M (ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1))) := rfl
theorem tmpK2_some : tmpK2 vis rP M (some (hd, m2)) =
    if 4294967296 ≤ hd then none
    else tmpK3 vis rP (mknF m2 [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)]) := rfl
theorem tmpK3_some : tmpK3 vis rP (some (r3, m3)) =
    tmpK4 (stubM "infer_type_core" m3 [vis, rP, r3.headD 0]) := rfl
theorem tmpK4_some : tmpK4 (some (r4, m4)) = some ([], m4) := rfl
end arms

grind_pattern [ind_grind] tmpW_mem => tmpW (N + 1) m vis rP M
grind_pattern [ind_grind] tmpW_out => tmpW (N + 1) m vis rP M
grind_pattern [ind_grind] tmpK1_some => tmpK1 vis rP M (some (r1, m1))
grind_pattern [ind_grind] tmpK2_some => tmpK2 vis rP M (some (hd, m2))
grind_pattern [ind_grind] tmpK3_some => tmpK3 vis rP (some (r3, m3))
grind_pattern [ind_grind] tmpK4_some => tmpK4 (some (r4, m4))

/-- The lookups `target_major_pins` needs. -/
structure TmpProg (p : Prog) : Prop where
  ad : AdF p
  tpt : p.lookup "target_pin_tys" = some targetPinTys
  cf : p.lookup "const_find" = some constFind
  cp : p.lookup "const_push" = some constPush
  ic : p.lookup "intern_const" = some internConst
  tmp : p.lookup "target_major_pins" = some targetMajorPins

theorem targetMajorPins_spec (p : Prog) (h : TmpProg p) (N : Nat) (s₀ : St) (vis rP M : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, M]
    ⦃fun r s' => LocEq s' s₀ ∧ tmpW N s₀.mem vis rP M = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.tmp]
  simp only [callFn, targetMajorPins]
  cases N with
  | zero => vcgen [exec] <;> grind
  | succ N =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        targetPinTys_spec p h.tpt N, internConst_spec p h.cf h.cp h.ic N,
        mknF_spec p h.ad N, stubM_spec p "infer_type_core" N] <;>
      finish (gen := 20) [rdW_eq]


theorem decTM_ds {m : Mem} {p : Nat} {M : TargetMajor} (h : decTM m p = some M) :
    ∃ o l, iwN m (p + 2) = some o ∧ iwN m (p + 3) = some l ∧ decHL m o l = some M.ds := by
  simp only [decTM, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
  obtain ⟨w5, h5, a1, ha1, w4, h4, w3, h3, w2, h2, ac, hac, w1, hw1, w0, h0, a, ha, rfl⟩ := h
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some h4
  exact ⟨o, l, ho, by simpa using hl, hd⟩

/-- A non-empty slice decoded below the tops ends below the top. -/
theorem decHL_truncM_bound {k : IdxKind} {m : Mem} {o l : Nat} {xs : List (Idx k)}
    (h : decHL (truncM m) o l = some xs) (hl : l ≠ 0) : o + l ≤ iwTop m := by
  have := decHL_getI h (l - 1) (by omega)
  simp only [iwH, hd?] at this
  cases hw : (iwA (truncM m))[o + (l - 1)]? with
  | none => simp [hw] at this
  | some w =>
    have := (truncM_iw_get hw).1
    omega

theorem tmpW_ok {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {N : Nat} {m m' : Mem} {rP Mp : Word} {r : List Word} {M : TargetMajor}
    (h : tmpW N m vis rP Mp = some (r, m')) (hS : StageR dn vis fe m a)
    (hM : DecB (fun m => decTM m Mp.toNat) m M) :
    ∃ a', (ConRon.Arena.targetMajorPins V fe rP.toNat M).run a = .ok ((), a') ∧
      StageR dn vis fe m' a' ∧ IWGrow m m' := by
  cases N with
  | zero => simp [tmpW] at h
  | succ N =>
  have hsz := hS.2.2.2.1
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨k, hk, hmem⟩ := decTM_member hM0
  have hrk := iwN_rdW_at (w := Mp) (k := 8) hk hsz
  rw [show UInt64.ofNat 8 = (8 : Word) from rfl] at hrk
  by_cases hk0 : rdW (m.arr64 IW) (Mp + 8) ≠ 0
  · rw [tmpW_mem (h := hk0)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hk0' : k ≠ 0 := by intro e; apply hk0; rw [hrk.1, e]; rfl
    have hmem' : M.member = some (k - 1) := by rw [hmem]; simp [decON, hk0']
    exact ⟨a, by simp [ConRon.Arena.targetMajorPins, hmem']; rfl, hS, IWGrow.refl m⟩
  rw [tmpW_out (h := hk0)] at h
  have hk00 : k = 0 := by
    have : rdW (m.arr64 IW) (Mp + 8) = 0 := by simpa using hk0
    rw [hrk.1] at this
    have := congrArg UInt64.toNat this
    rwa [UInt64.toNat_ofNat_of_lt' hrk.2] at this
  have hmem' : M.member = none := by rw [hmem, hk00]; rfl
  obtain ⟨o, l, hoT, hlT, hdT⟩ := decTM_ds (show decTM (truncM m) Mp.toNat = some M from hM)
  obtain ⟨hoi, ho⟩ := iwN_truncM_get hoT
  obtain ⟨hli, hl⟩ := iwN_truncM_get hlT
  have hds : decHL m o l = some M.ds := (OMono.decHL o l).mono _ _ _ (IWGrow.refl m).truncExt hdT
  have ro := iwN_rdW_at (w := Mp) (k := 2) ho hsz
  have rl := iwN_rdW_at (w := Mp) (k := 3) hl hsz
  rw [show UInt64.ofNat 2 = (2 : Word) from rfl] at ro
  rw [show UInt64.ofNat 3 = (3 : Word) from rfl] at rl
  rw [ro.1, rl.1] at h
  have hoo := UInt64.toNat_ofNat_of_lt' ro.2
  have hll := UInt64.toNat_ofNat_of_lt' rl.2
  -- the pins of the parameters
  obtain ⟨a1, m1, r1, h1, hrun1, hS1, hg1⟩ : ∃ a1 m1 r1,
      tptW N m vis rP (UInt64.ofNat o) (UInt64.ofNat l) = some (r1, m1) ∧
      (ConRon.Arena.targetPinTys V fe rP.toNat M.ds).run a = .ok ((), a1) ∧
      StageR dn vis fe m1 a1 ∧ IWGrow m m1 := by
    cases h1 : tptW N m vis rP (UInt64.ofNat o) (UInt64.ofNat l) with
    | none => rw [h1] at h; simp [tmpK1] at h
    | some rm1 =>
    obtain ⟨r1, m1⟩ := rm1
    by_cases hl0 : l = 0
    · subst hl0
      have hnil : M.ds = [] := by simpa [decHL, hslice?] using hds.symm
      cases N with
      | zero => simp [tptW] at h1
      | succ N =>
      rw [tptW_nil N m vis rP (UInt64.ofNat o) (UInt64.ofNat 0) rfl] at h1
      simp only [Option.some.injEq, Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact ⟨a, m, [], rfl, by rw [hnil]; rfl, hS, IWGrow.refl m⟩
    have hbnd := decHL_truncM_bound hdT hl0
    obtain ⟨a1, hrun1, hS1, hg1⟩ := tptW_ok dn fe N m m1 a vis rP _ _ r1 M.ds h1 hS
      (by rw [hoo, hll]; exact hds) (by rw [hoo, hll]; have := hS.2.1; omega) (by rw [hoo, hll]; exact hbnd)
    exact ⟨a1, m1, r1, rfl, hrun1, hS1, hg1⟩
  rw [h1, tmpK1_some] at h
  have hM1 : decTM m1 Mp.toNat = some M := hM.stab (decTM_mono _) m1 hg1
  obtain ⟨wi, hwi, hwiH, hwiE⟩ := iwH_rdW_at (w := Mp) (k := 0) (by simpa using decTM_ind hM1) hS1.2.2.2.1
  obtain ⟨wu, hwu, hwuH, hwuE⟩ := iwH_rdW_at (w := Mp) (k := 1) (decTM_lvls' hM1) hS1.2.2.2.1
  rw [show Mp + UInt64.ofNat 0 = Mp by simp] at hwi
  rw [show UInt64.ofNat 1 = (1 : Word) from rfl] at hwu
  rw [hwi, hwu] at h
  cases h2 : ceinternW m1 wi wu with
  | none => rw [h2] at h; simp [tmpK2] at h
  | some rm2 =>
  obtain ⟨hd, m2⟩ := rm2
  rw [h2, tmpK2_some] at h
  obtain ⟨a2, hrun2, hS2, hg2⟩ := internConst_stage hS1 wi wu hwiH hwuH h2
  by_cases hbig : 4294967296 ≤ hd
  · rw [if_pos hbig] at h; cases h
  rw [if_neg hbig] at h
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
  cases h3 : mknF m2 [hd, UInt64.ofNat o, UInt64.ofNat l] with
  | none => rw [h3] at h; simp [tmpK3] at h
  | some rm3 =>
  obtain ⟨r3, m3⟩ := rm3
  rw [h3, tmpK3_some] at h
  have hds2 : decHL m2 (UInt64.ofNat o).toNat (UInt64.ofNat l).toNat = some M.ds := by
    rw [hoo, hll]; exact (OMono.decHL o l).mono _ _ _ hg12.truncExt hdT
  obtain ⟨x3, a3, hrun3, hS3, hg3, hx3⟩ := mknF_ok dn vis fe hd _ _ hdH M.ds m2 m3 a2 r3 h3 ⟨hS2, hds2⟩
  cases h4 : stubM "infer_type_core" m3 [vis, rP, r3.headD 0] with
  | none => rw [h4] at h; simp [tmpK4] at h
  | some rm4 =>
  obtain ⟨r4, m4⟩ := rm4
  rw [h4, tmpK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨x4, a4, hrun4, hS4, hg4, -⟩ := inferTypeCore_spec dn vis fe rP (r3.headD 0) hx3.1 m3 m4 a3 r4 h4 hS3
  rw [hx3.2] at hrun4
  rw [hwiE, hwuE] at hrun2
  have hrun3' : (mkAppN (decE hd) M.ds).run a2 = .ok (x3, a3) := hrun3
  refine ⟨a4, ?_, hS4, (hg12.trans hg3).trans hg4⟩
  simp only [ConRon.Arena.targetMajorPins, hmem', StateT.run_bind, hrun1, exc_ok_bind',
    internConstE, hrun2, hrun3', hrun4]
  rfl

/-- **`target_major_pins` refines `targetMajorPins`** (through `target_pin_tys`'s and the stubs
`mk_app_n_f`, `infer_type_core`; the interned head guarded below `2^32`). -/
@[refines ConRon.Arena.targetMajorPins]
theorem targetMajorPins_refines (p : Prog) (hp : TmpProg p) (N : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (rP Mp : Word) (M : TargetMajor)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : DecB (fun m => decTM m Mp.toNat) s₀.mem M) :
    ⦃fun s => s = s₀⦄ invoke p (exec p N) "target_major_pins" [vis, rP, Mp]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.targetMajorPins V fe rP.toNat M) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ := by
  refine triple_post (targetMajorPins_spec p hp N s₀ vis rP Mp) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨a', hrun, hS', hg⟩ := tmpW_ok hm hS hM
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg⟩

end L.Ind
