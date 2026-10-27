import ConAgua.Arena.DefEqMidQuick
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.WhnfIotaRefine

/-!
# The same-head spine comparison: `defeq_spine` (lane `defeq`)

`defeqSpine` split for the proofs (`DefEq.lean`): `spine_head` (the head through `get_app_fn`, a
constant's name and levels through `e_view`), `spine_cmp` (names, lengths, levels, then
`defeq_list_rev` on the two argument slices), `defeq_spine2` (the two argument slices pushed by
`get_app_args`, `spine_cmp`, the stack top put back), `defeq_spine` (both heads, then
`defeq_spine2`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of this file. -/
structure SpineDProg (p : Prog) : Prop where
  quick : QuickProg p
  head : p.lookup "spine_head" = some spineHeadL
  cmp : p.lookup "spine_cmp" = some spineCmpL
  sp2 : p.lookup "defeq_spine2" = some defeqSpine2L
  sp : p.lookup "defeq_spine" = some defeqSpineL
  rev : p.lookup "defeq_list_rev" = some defeqListRevL

theorem SpineDProg.spine {p : Prog} (hp : SpineDProg p) : SpineProg p :=
  hp.quick.lams.mid.leaf.core.spine

theorem SpineDProg.leaf {p : Prog} (hp : SpineDProg p) : DefEqLeafProg p := hp.quick.lams.mid.leaf

/-! ## `spine_head` -/

/-- A spine's constant head, as the twin reads it in `defeqSpine`. -/
def spineHeadT (e : EIdx) : AM (Option (NIdx × LsIdx)) := do
  let hh ← getAppFn coreWalkFuel e
  if hh.tag == ETag.const then
    match ← view hh with
    | .const n us => pure (some (n, us))
    | _ => pure none
  else pure none

/-- `(f, n, us)`. -/
def decSH (r : List Word) : Option (NIdx × LsIdx) :=
  if r.headD 0 = 0 then none else some (decI (r.tail.headD 0), decI (r.tail.tail.headD 0))

/-- **`spine_head` is its model `shW`** (generated). -/
l_model spineHead_spec (p : Prog) (hp : SpineDProg p)
  fns [hp.head ↦ shW tuple]
  specs [callW_spec p n "get_app_fn", callW_spec p n "e_view"]
  grind [arena_grind] simp [St.setLocs_mem']

theorem viewR_const {r : List Word} {v : ENodeView} (hr : L.Ind.ViewR r v) (h3 : r.headD 0 = 3) :
    v = .const (decI (r.tail.headD 0)) (decI (r.tail.tail.headD 0)) ∧ HW (r.tail.headD 0) ∧
      HW (r.tail.tail.headD 0) := by
  cases v <;> simp only [L.Ind.ViewR, h3] at hr
  all_goals first
    | (exfalso; obtain ⟨h0, -⟩ := hr; revert h0; decide)
    | (exfalso; revert hr; decide)
    | (obtain ⟨-, h1, h4, h5, h6⟩ := hr; rw [getD_one] at h1 h4; rw [getD_two] at h5 h6
       exact ⟨by rw [h4, h6], h1, h5⟩)

/-- **A run of `spine_head`**: the memory kept, the twin's `spineHeadT` without a state change, a
found head's view. -/
theorem spineHead_run {p : Prog} (hp : SpineDProg p) {n : Nat} {m m' : Mem} {a₀ : AState}
    (hR : ArenaR m a₀) {e : Word} (he : HW e) {r : List Word}
    (hc : callW p (n + 1) "spine_head" [e] m = some (r, m')) :
    m' = m ∧ (spineHeadT (decE e)).run a₀ = .ok (decSH r, a₀) ∧ Res3 r ∧
      (r.headD 0 ≠ 0 → ∃ h, a₀.store.view h =
        some (.const (decI (r.tail.headD 0)) (decI (r.tail.tail.headD 0)))) := by
  obtain ⟨s', hm', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (spineHead_spec p hp (n + 1) ⟨m, Locals.init []⟩ e) hc
  rw [← hm', shW.arm1] at *
  cases hc1 : callW p n "get_app_fn" [e] m with
  | none => rw [hc1, shW.k_get_app_fn.none] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨hm1, hh, hgaf⟩ := getAppFn_callW hp.leaf hR he hc1
  rw [hm1] at hW
  have hT : (spineHeadT (decE e)).run a₀ = (if (decE (r₁.headD 0)).tag == ETag.const then do
      match ← view (decE (r₁.headD 0)) with
      | .const n us => pure (some (n, us))
      | _ => pure none
    else pure none : AM (Option (NIdx × LsIdx))).run a₀ := by
    simp only [spineHeadT, StateT.run_bind, hgaf, except_ok_bind]
  rw [tag_beq_w _ hh 3 (by decide) ETag.const rfl 3 rfl] at hT
  by_cases h3 : r₁.headD 0 >>> 28 ≠ 3
  · rw [shW.k_get_app_fn.arm1 (hc1 := h3), Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
    obtain ⟨g1, g2, g3, hm⟩ := hW
    simp only [h3, decide_false, Bool.false_eq_true, ↓reduceIte] at hT
    refine ⟨hm.symm, by rw [hT]; simp only [decSH, ← g1, ↓reduceIte]; rfl,
      res3_of hw0 hw0 hw0 g1 g2 g3, fun h => absurd g1.symm h⟩
  have h3' : r₁.headD 0 >>> 28 = 3 := by simpa using h3
  rw [shW.k_get_app_fn.arm2 (hc1 := h3')] at hW
  cases hc2 : callW p n "e_view" [r₁.headD 0] m with
  | none => rw [hc2, shW.k_e_view.none] at hW; cases hW
  | some q =>
  obtain ⟨rv, m₂⟩ := q
  rw [hc2, shW.k_e_view.arm1, Option.some.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hW
  obtain ⟨g1, g2, g3, hm⟩ := hW
  obtain ⟨hm2, v, hv, hvr, ht⟩ := eView_callW_view (a := a₀) hp.quick.lams.peel.eview hR hc2
  rw [hm2] at hm
  obtain ⟨rfl, hw1', hw2'⟩ := viewR_const hvr (ht.trans h3')
  simp only [h3', decide_true, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv,
    except_ok_bind] at hT
  refine ⟨hm.symm, by rw [hT]; simp only [decSH, ← g1, ← g2, ← g3]; rfl,
    res3_of hw1 hw1' hw2' g1 g2 g3, fun _ => ⟨_, by rw [hv, ← g2, ← g3]⟩⟩

/-! ## `spine_cmp` -/

/-- `defeqSpine`'s comparison past the two heads and the two argument lists. -/
def spineCmpT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (n : NIdx) (us : LsIdx) (n' : NIdx)
    (us' : LsIdx) (aa bb : List EIdx) : AM Bool :=
  if n = n' ∧ aa.length = bb.length then do
    match ← lvlsEq? us us' with
    | some true => defEqList r fe depth aa.reverse bb.reverse
    | _ => pure false
  else pure false

/-- **`spine_cmp` is its model `scW`** (generated). -/
l_model spineCmp_spec (p : Prog) (hp : SpineDProg p)
  fns [hp.cmp ↦ scW]
  specs [callW_spec p n "lvls_eq_c", callW_spec p n "defeq_list_rev"]
  grind [arena_grind] simp []

/-- `lvls_eq_c` does not return at fuel `1`. -/
theorem lvlsEqC_one (p : Prog) (hp : LvlCacheProg p) (u v : Word) (m m' : Mem) (r : List Word) :
    callW p 1 "lvls_eq_c" [u, v] m ≠ some (r, m') := by
  intro hc
  have h : ⦃fun s => s = (⟨m, Locals.init []⟩ : St)⦄ invoke p (exec p 1) "lvls_eq_c" [u, v]
      ⦃fun _ _ => False; ⊤⦄ := by
    rw [invoke_eq _ hp.cs]
    simp only [callFn, lvlsEqCL]
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, invoke_zero_false p "lsq_find",
      invoke_zero_false p "lvls_eq_rec"] <;> grind
  obtain ⟨_, _, hf⟩ := triple_of_callW h hc
  exact hf

theorem decO_two {w : Word} (h : 2 ≤ w) : decO w = some true := by
  unfold decO
  have h0 : w ≠ 0 := fun e => by subst e; revert h; decide
  have h1 : w ≠ 1 := fun e => by subst e; revert h; decide
  simp [h0, h1]

theorem decO_lt_two {w : Word} (h : ¬ 2 ≤ w) : decO w ≠ some true := by
  have : w = 0 ∨ w = 1 := by
    have : w.toNat < 2 := by
      have : ¬ (2 : Word).toNat ≤ w.toNat := fun h' => h (UInt64.le_iff_toNat_le.mpr h')
      simp at this; omega
    rcases (show w.toNat = 0 ∨ w.toNat = 1 by omega) with e | e
    · exact .inl (UInt64.toNat_inj.mp (by simpa using e))
    · exact .inr (UInt64.toNat_inj.mp (by simpa using e))
  rcases this with rfl | rfl <;> decide

/-- **`spine_cmp` refines `spineCmpT`** on two slices below the stack top, at the knot. -/
theorem spineCmp_refines (p : Prog) (hp : SpineDProg p) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d nm us nm₂ us₂ ao an bo bn : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hnm : HW nm) (hnm₂ : HW nm₂) (hus : HW us)
    (hus₂ : HW us₂) (lu lv : List ConLeche.Level) (_hdu : denoteLs a₀.store.lss (decI us) = some lu)
    (_hdv : denoteLs a₀.store.lss (decI us₂) = some lv) (xs ys : List EIdx)
    (hx : SpineR s₀.mem ao an xs.toArray) (hy : SpineR s₀.mem bo bn ys.toArray)
    (hxt : ao.toNat + an.toNat ≤ (spTop s₀.mem).toNat)
    (hyt : bo.toNat + bn.toNat ≤ (spTop s₀.mem).toNat) :
    CoreSpec p (n + 1) "spine_cmp" [mode, vis, d, nm, us, nm₂, us₂, ao, an, bo, bn]
      (spineCmpT (coreKnot (decMode mode) fe id F) fe d.toNat (decI nm) (decI us) (decI nm₂) (decI us₂)
        xs ys) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (spineCmp_spec p hp (n + 1) s₀ mode vis d nm us nm₂ us₂ ao an bo bn)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hxl := slice_len hx
  have hyl := slice_len hy
  have hcond : (decI nm = (decI nm₂ : NIdx) ∧ xs.reverse.length = ys.reverse.length) ↔
      (nm = nm₂ ∧ an = bn) := by
    rw [List.length_reverse, List.length_reverse, hxl, hyl]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by have := decI_beq (k := .name) nm nm₂ hnm hnm₂; rw [h1, beq_self_eq_true] at this
                simpa using this, UInt64.toNat_inj.mp h2⟩
    · rintro ⟨rfl, rfl⟩; exact ⟨rfl, rfl⟩
  unfold spineCmpT
  by_cases hc : nm = nm₂ ∧ an = bn
  · rw [scW.arm1 (hc1 := hc)] at hW
    have hc' : decI nm = (decI nm₂ : NIdx) ∧ xs.length = ys.length := by
      have := hcond.mpr hc; simpa using this
    rw [ite_eq_left hc']
    cases hc2 : callW p n "lvls_eq_c" [us, us₂] s.mem with
    | none => rw [hc2, scW.k_lvls_eq_c.none] at hW; cases hW
    | some q =>
    obtain ⟨rz, m₁⟩ := q
    rw [hc2] at hW
    obtain ⟨n₁, rfl⟩ := callW_succ hc2
    cases n₁ with
    | zero => exact absurd hc2 (lvlsEqC_one p hp.quick.lv _ _ _ _ _)
    | succ n₂ =>
    have e₁ := CoreSpec.of_callW (s₀ := ⟨s.mem, Locals.init []⟩)
      (lvlsEqC_refines p hp.quick.lv n₂ ⟨s.mem, Locals.init []⟩ a₀ dn vis fe M eb hS us us₂ hus
        hus₂) hc2
    refine coreRef_bindS e₁ (fun M₁ hS₁ hst₁ => ?_)
    by_cases h2 : 2 ≤ rz.headD 0
    · rw [scW.k_lvls_eq_c.arm1 (hc1 := h2)] at hW
      rw [decO_two h2]
      exact CoreSpec.of_call1W (s₀ := ⟨m₁, Locals.init []⟩)
        (defeqListRev_refines p hp.rev (n₂ + 1) (hk.mono (by omega)) F (by omega) (by omega) _ _
          dn vis fe M₁ eb mode d ao an bo bn ⟨hS₁, hs.mode4, hs.eb_mode⟩ xs ys
          (hx.keep hst₁.size hst₁.below hxt hS.spn) (hy.keep hst₁.size hst₁.below hyt hS.spn)
          (hst₁.1 ▸ hxt) (hst₁.1 ▸ hyt))
        (fun r r' h => by simp only [decBool, h]) hW
    · rw [scW.k_lvls_eq_c.arm2 (hc1 := h2), scW.j1.arm1, Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr, hm⟩ := hW
      have hne := decO_lt_two h2
      rw [← hm]
      generalize decO (rz.headD 0) = o at hne
      rcases o with _ | ⟨_ | _⟩
      · exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
      · exact coreRef_ret hS₁ (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
      · exact absurd rfl hne
  · rw [scW.arm2 (hc1 := hc), scW.j1.arm1, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hc' : ¬ (decI nm = (decI nm₂ : NIdx) ∧ xs.length = ys.length) := by
      intro h; apply hc; apply hcond.mp; simpa using h
    rw [ite_eq_right hc', ← hm]
    exact coreRef_ret hS (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)

/-! ## `defeq_spine2` -/

/-- `defeqSpine` past the two heads: the two argument lists, then `spineCmpT`. -/
def spine2T (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (n : NIdx) (us : LsIdx)
    (n' : NIdx) (us' : LsIdx) : AM Bool := do
  let aa ← getAppArgs coreWalkFuel a
  let bb ← getAppArgs coreWalkFuel b
  spineCmpT r fe depth n us n' us' aa bb

/-- **`defeq_spine2` is its model `s2W`** (generated). -/
l_model defeqSpine2_spec (p : Prog) (hp : SpineDProg p)
  fns [hp.sp2 ↦ s2W]
  specs [callW_spec p n "get_app_args", callW_spec p n "spine_cmp"]
  grind [arena_grind] simp [rdW_eq, St.setLocs_mem']

/-- **`defeq_spine2` refines `spine2T`** at the knot: the two argument slices pushed, compared, the
stack top put back. -/
theorem defeqSpine2_refines (p : Prog) (hp : SpineDProg p) (n : Nat) (hk : KnotUpTo p n) (F : Nat)
    (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b nm us nm₂ us₂ : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) (hnm : HW nm) (hnm₂ : HW nm₂)
    (hus : HW us) (hus₂ : HW us₂) (lu lv : List ConLeche.Level)
    (hdu : denoteLs a₀.store.lss (decI us) = some lu) (hdv : denoteLs a₀.store.lss (decI us₂) = some lv) :
    CoreSpec p (n + 1) "defeq_spine2" [mode, vis, d, a, b, nm, us, nm₂, us₂]
      (spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decI nm) (decI us)
        (decI nm₂) (decI us₂)) decBool s₀ a₀ dn vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqSpine2_spec p hp (n + 1) s₀ mode vis d a b nm us nm₂ us₂)
  subst hs0
  rw [s2W.arm1] at hW
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  cases hc1 : callW p n "get_app_args" [a] s.mem with
  | none => rw [hc1, s2W.k_get_app_args.none] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1, s2W.k_get_app_args.arm1] at hW
  obtain ⟨t₁, ht₁, -, hfr₁, hg₁, ho₁, htop₁, xs, hxs, hx₁⟩ := triple_of_callW
    (s₀ := ⟨s.mem, Locals.init []⟩)
    (getAppArgs_refines p hp.spine n ⟨s.mem, Locals.init []⟩ a₀ hS.arena.1 a ha hS.spn) hc1
  rw [ht₁] at hfr₁ hg₁ htop₁ hx₁
  have hS₁ := hS.frame_stk hfr₁ (by simp) (by simp)
  cases hc2 : callW p n "get_app_args" [b] m₁ with
  | none => rw [hc2, s2W.k_get_app_args_2.none] at hW; cases hW
  | some q =>
  obtain ⟨r₂, m₂⟩ := q
  rw [hc2, s2W.k_get_app_args_2.arm1] at hW
  obtain ⟨t₂, ht₂, -, hfr₂, hg₂, ho₂, htop₂, ys, hys, hy₂⟩ := triple_of_callW
    (s₀ := ⟨m₁, Locals.init []⟩)
    (getAppArgs_refines p hp.spine n ⟨m₁, Locals.init []⟩ a₀ hS₁.arena.1 b hb hS₁.spn) hc2
  rw [ht₂] at hfr₂ hg₂ htop₂ hy₂
  have hS₂ := hS₁.frame_stk hfr₂ (by simp) (by simp)
  -- the first slice survives the second push
  have hb₁ := hx₁.bound
  have hb₂ := hy₂.bound
  have hsp₁ := hS₁.spn
  have htop₁' : (spTop m₁).toNat = (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat := by
    rw [htop₁, UInt64.toNat_add, ← ho₁]; omega
  have htop₂' : (spTop m₂).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
    have hsz₂ : (m₂.arr64 SPN).size = (m₁.arr64 SPN).size := hg₂.size
    rw [htop₂, UInt64.toNat_add, ← ho₂]; omega
  have hle : (spTop m₁).toNat ≤ (spTop m₂).toNat := UInt64.le_iff_toNat_le.mp hg₂.1
  have hx₂ := hx₁.keep hg₂.size hg₂.below (by omega) hsp₁
  cases hc3 : callW p n "spine_cmp" [mode, vis, d, nm, us, nm₂, us₂, r₁.headD 0, r₁.tail.headD 0,
      r₂.headD 0, r₂.tail.headD 0] m₂ with
  | none => rw [hc3, s2W.k_spine_cmp.none] at hW; cases hW
  | some q =>
  obtain ⟨r₃, m₃⟩ := q
  rw [hc3, s2W.k_spine_cmp.arm1] at hW
  obtain ⟨n', rfl⟩ := callW_succ hc3
  have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (spineCmp_refines p hp n' (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩ a₀ dn
      vis fe M eb mode d nm us nm₂ us₂ _ _ _ _ ⟨hS₂, hs.mode4, hs.eb_mode⟩ hnm hnm₂ hus hus₂ lu lv hdu hdv
      xs ys hx₂ hy₂ (by show _ ≤ (spTop m₂).toNat; omega) (by show _ ≤ (spTop m₂).toNat; omega)) hc3
  · simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hT : (spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b) (decI nm)
        (decI us) (decI nm₂) (decI us₂)).run a₀ = (spineCmpT (coreKnot (decMode mode) fe id F) fe
          d.toNat (decI nm) (decI us) (decI nm₂) (decI us₂) xs ys).run a₀ := by
      simp only [spine2T, StateT.run_bind, hxs, hys, except_ok_bind]
    obtain ⟨g1, ⟨M₃, hS₃, hK₃, hst₃⟩, g3, g4⟩ := e₃
    have h136 : 136 < (m₃.arr64 CTL).size := by
      obtain ⟨mp, h⟩ := hS₃.memos.2.2.2.2.1
      unfold MemoRG MemoRV at h
      have := h.1
      simp only at this
      have e : (156 : Word).toNat = 156 := rfl
      omega
    have hG : GrowRefP (spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
        (decI nm) (decI us) (decI nm₂) (decI us₂)) a₀ decBool dn s.mem vis fe M eb r₃ m₃ :=
      growRef_congr hT ⟨g1, ⟨M₃, hS₃, hK₃, hg₁.trans' (hg₂.trans' hst₃.toGrew')⟩, g3, g4⟩
    have hR := GrowRefP.reset hG h136
    rw [← hm]
    exact coreRef_redec hR (by simp only [decBool, hr]) (by unfold ResH; rw [← hr]; exact g4)

/-! ## `defeq_spine` -/

theorem defeqSpine_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    defeqSpine r fe depth a b = (spineHeadT a >>= fun o => match o with
      | none => pure false
      | some (n, us) => spineHeadT b >>= fun o' => match o' with
        | none => pure false
        | some (n', us') => spine2T r fe depth a b n us n' us') := by
  unfold defeqSpine spineHeadT spine2T spineCmpT
  simp only [bind_assoc]
  congr 1; funext hh
  split
  · simp only [bind_assoc]
    congr 1; funext v
    cases v <;> simp only [pure_bind]
    congr 1; funext hh'
    split
    · simp only [bind_assoc]
      congr 1; funext v'
      cases v' <;> simp only [pure_bind]
      rfl
    · simp only [pure_bind]
  · simp only [pure_bind]

/-- **`defeq_spine` is its model `dsW`** (generated). -/
l_model defeqSpine_spec (p : Prog) (hp : SpineDProg p)
  fns [hp.sp ↦ dsW]
  specs [callW_spec p n "spine_head", callW_spec p n "defeq_spine2"]
  grind [arena_grind] simp [St.setLocs_mem']

theorem decSH_none {r : List Word} (h : r.headD 0 = 0) : decSH r = none := by
  simp only [decSH, h, ↓reduceIte]

theorem decSH_some {r : List Word} (h : r.headD 0 ≠ 0) :
    decSH r = some (decI (r.tail.headD 0), decI (r.tail.tail.headD 0)) := by
  simp only [decSH, h, ↓reduceIte]

/-- **`defeq_spine` refines `defeqSpine`** at the knot. -/
@[refines ConRon.Arena.defeqSpine]
theorem defeqSpine_refines (p : Prog) (hp : SpineDProg p) (hsd : StoreDenotes) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb mode d a b : Word)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b) :
    CoreSpec p (n + 1) "defeq_spine" [mode, vis, d, a, b]
      (defeqSpine (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe M eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (defeqSpine_spec p hp (n + 1) s₀ mode vis d a b)
  subst hs0
  rw [dsW.arm1] at hW
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  rw [defeqSpine_eq]
  cases hc1 : callW p n "spine_head" [a] s.mem with
  | none => rw [hc1, dsW.k_spine_head.none] at hW; cases hW
  | some q =>
  obtain ⟨ra, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨k, rfl⟩ := callW_succ hc1
  obtain ⟨hm₁, hra, ⟨hra0, hra1, hra2⟩, hva⟩ := spineHead_run hp hS.arena.1 ha hc1
  rw [hm₁] at hW
  by_cases h0 : ra.headD 0 = 0
  · rw [dsW.k_spine_head.arm1 (hc1 := h0), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [← hm]
    refine coreRef_pure' hS (v := false) ?_ (by rw [decBool, ← hr]; rfl)
      (by unfold ResH; rw [← hr]; exact hw0)
    rw [StateT.run_bind, hra, except_ok_bind, decSH_none h0]; rfl
  rw [dsW.k_spine_head.arm2 (hc1 := h0)] at hW
  cases hc2 : callW p (k + 1) "spine_head" [b] s.mem with
  | none => rw [hc2, dsW.k_spine_head_2.none] at hW; cases hW
  | some q =>
  obtain ⟨rb, m₂⟩ := q
  rw [hc2] at hW
  obtain ⟨hm₂, hrb, ⟨hrb0, hrb1, hrb2⟩, hvb⟩ := spineHead_run hp hS.arena.1 hb hc2
  rw [hm₂] at hW
  have hT₁ : ((spineHeadT (decE a) >>= fun o => match o with
      | none => pure false
      | some (n, us) => spineHeadT (decE b) >>= fun o' => match o' with
        | none => pure false
        | some (n', us') => spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
            n us n' us') : AM Bool).run a₀ =
      ((match decSH rb with
        | none => pure false
        | some (n', us') => spine2T (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
            (decI (ra.tail.headD 0)) (decI (ra.tail.tail.headD 0)) n' us') : AM Bool).run a₀ := by
    rw [StateT.run_bind, hra, except_ok_bind, decSH_some h0]
    simp only [StateT.run_bind, hrb, except_ok_bind]
  refine coreRef_congr hT₁ ?_
  by_cases h0' : rb.headD 0 = 0
  · rw [dsW.k_spine_head_2.arm1 (hc1 := h0'), Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [decSH_none h0', ← hm]
    exact coreRef_ret hS (by rw [decBool, ← hr]; rfl) (by unfold ResH; rw [← hr]; exact hw0)
  rw [dsW.k_spine_head_2.arm2 (hc1 := h0')] at hW
  rw [decSH_some h0']
  obtain ⟨ha', hva'⟩ := hva h0
  obtain ⟨hb', hvb'⟩ := hvb h0'
  obtain ⟨lu, hdu⟩ := hsd.constLs dn s.mem a₀ vis fe M eb hS _ _ _ hva'
  obtain ⟨lv, hdv⟩ := hsd.constLs dn s.mem a₀ vis fe M eb hS _ _ _ hvb'
  exact CoreSpec.of_call1W (s₀ := ⟨s.mem, Locals.init []⟩)
    (defeqSpine2_refines p hp k (hk.mono (by omega)) F (by omega) (by omega) ⟨s.mem, Locals.init []⟩
      a₀ dn vis fe M eb mode d a b _ _ _ _ ⟨hS, hs.mode4, hs.eb_mode⟩ ha hb hra1 hrb1 hra2 hrb2 lu lv hdu hdv)
    (fun r r' h => by simp only [decBool, h]) hW

end L.Arena
