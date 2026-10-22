import ConAgua.Arena.RecCheckSpec7
import ConAgua.Arena.RecGenSpec11
import ConAgua.Arena.DeclCanonView2

/-!
# `RecCheck`: `auxRuleFire` (lane `indproofs2`, helper `rec3`)

`view_ls` is lane `decls3`'s word model (`viewLsW`, `viewLsW_ok`), `abstract_prefix_list` helper
`rec`'s (`aplW_ok`).
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

def arfK2 (r1 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => some ([1, r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0], m2)

def arfK1 (n : Nat) (M rP : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => arfK2 r1 (aplW n m1 rP (rdW (m1.arr64 IW) (M + 2)) (rdW (m1.arr64 IW) (M + 3)))

/-- **The model of `aux_rule_fire`.** -/
def arfW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, M, rP => arfK1 n M rP (viewLsW n m (rdW (m.arr64 IW) (M + 1)))

section arms
variable (n : Nat) (m m1 m2 : Mem) (M rP : Word) (r1 r2 : List Word)
theorem arfW_eq : arfW (n + 1) m M rP = arfK1 n M rP (viewLsW n m (rdW (m.arr64 IW) (M + 1))) := rfl
theorem arfK1_some : arfK1 n M rP (some (r1, m1)) =
    arfK2 r1 (aplW n m1 rP (rdW (m1.arr64 IW) (M + 2)) (rdW (m1.arr64 IW) (M + 3))) := rfl
theorem arfK2_some : arfK2 r1 (some (r2, m2)) =
    some ([1, r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0], m2) := rfl
end arms
attribute [ind_grind] arfW_eq arfK1_some arfK2_some

/-- The lookups `aux_rule_fire` needs. -/
structure ArfLook (p : Prog) : Prop where
  ln : p.lookup "ls_node" = some lsNode
  alloc : p.lookup "iw_alloc" = some iwAlloc
  pc : p.lookup "pool_copy" = some poolCopy
  vl : p.lookup "view_ls" = some viewLsL
  ap : p.lookup "abstract_prefix" = some abstractPrefix
  copy : p.lookup "iw_copy" = some iwCopy
  cons : p.lookup "sl_cons" = some slCons
  apl : p.lookup "abstract_prefix_list" = some abstractPrefixList
  arf : p.lookup "aux_rule_fire" = some auxRuleFire

theorem auxRuleFire_spec (p : Prog) (h : ArfLook p) (n : Nat) (s₀ : St) (M rP : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "aux_rule_fire" [M, rP]
    ⦃fun r s' => LocEq s' s₀ ∧ arfW n s₀.mem M rP = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.arf]
  simp only [callFn, auxRuleFire]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        viewLs_specW p h.ln h.alloc h.pc h.vl n,
        abstractPrefixList_spec p h.ap h.copy h.alloc h.cons h.apl n] <;>
      finish (gen := 20) [rdW_eq]

/-- The fire `(1, lvls, pins)` as words. -/
def decFire (m' : Mem) (r : List Word) : IRecRuleFire → Prop
  | .nested lvls pins => r.headD 0 = 1 ∧ decRL (fun m => decHL m) 1 m' r lvls ∧
      decRL (fun m => decHL m) 3 m' r pins
  | _ => False

theorem arfW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (M rP : Word) (TM : TargetMajor) (hS : StageR dn vis fe m a)
    (hM : DecB (fun m => decTM m M.toNat) m TM) (hP : PoolSmall m) :
    RSim (arfW n m M rP) (ConRon.Arena.auxRuleFire TM rP.toNat) a (KP dn vis fe m decFire) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [arfW_eq]
  have hsz := hS.2.2.2.1
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨-, hlv, ⟨o, l, ho, hl, hds⟩, -⟩ := rec2DecTM_parts hM0
  obtain ⟨vl, evl, hvlH, dvl⟩ := iwH_rdW_at (w := M) (k := 1) hlv hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at evl
  rw [evl]
  intro b hb
  cases h1 : viewLsW n m vl with
  | none => rw [h1] at hb; cases hb
  | some x1 =>
  obtain ⟨r1, m1⟩ := x1
  rw [h1, arfK1_some] at hb
  obtain ⟨ids, hrun1, hS1, hg1, hd1, -⟩ := viewLsW_ok h1 hS hvlH hP
  -- the `ds` slice, below the tops
  have h' : decTM (truncM m) M.toNat = some TM := hM
  obtain ⟨-, -, ⟨o', l', ho', hl', hds'⟩, -⟩ := rec2DecTM_parts h'
  obtain ⟨-, ho'm⟩ := rec2IwN_trunc ho'
  obtain ⟨-, hl'm⟩ := rec2IwN_trunc hl'
  have hsz1 := hS1.2.2.2.1
  obtain ⟨eo, to⟩ := rec2RdN (w := M) (k := 2) (by rw [iwN_grow hg1 (rec2IwN_trunc ho').1]; exact ho'm) hsz1
  obtain ⟨el, tl⟩ := rec2RdN (w := M) (k := 3) (by
    rw [iwN_grow hg1 (by have := (rec2IwN_trunc hl').1; simpa using this)]; simpa using hl'm) hsz1
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at eo el
  rw [eo, el] at hb
  have hdsDecB : DecB (fun m => (decHL m o' l' : Option (List EIdx))) m TM.ds := hds'
  have hds1 : decHL m1 (UInt64.ofNat o' : Word).toNat (UInt64.ofNat l' : Word).toNat = some TM.ds := by
    rw [to, tl]; exact hdsDecB.stab (OMono.decHL _ _) m1 hg1
  have hv1 := hd1
  simp only [decRL, getD_zero, Nat.zero_add, getD_one] at hv1
  obtain ⟨hv1d, hv1b⟩ := hv1
  rcases rec3IwSlice (show decHL (truncM m) o' l' = some TM.ds from hds') with hbnd | hl0
  · cases h2 : aplW n m1 rP (UInt64.ofNat o') (UInt64.ofNat l') with
    | none => rw [h2] at hb; cases hb
    | some x2 =>
    obtain ⟨r2, m2⟩ := x2
    rw [h2, arfK2_some] at hb
    cases hb
    obtain ⟨xs, a2, hrun2, hS2, hg2, hd2, ht2⟩ := aplW_ok dn vis fe n m1 m2 a rP _ _ r2 TM.ds h2 hS1 hds1
      (by rw [to, tl]; have := hS.2.1; omega) (by rw [to, tl]; have := hg1.1; omega) rP.toNat_lt
    refine ⟨.nested ids xs, a2, ?_, hS2, hg1.trans hg2, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [ConRon.Arena.auxRuleFire, StateT.run_bind]
      rw [← dvl, hrun1]
      simp only [bind, Except.bind]
      rw [hrun2]; rfl
    · show decHL m2 (r1.headD 0).toNat (r1.tail.headD 0).toNat = some ids
      rw [decHL_grow hg2 hv1b]; exact hv1d
    · show (r1.headD 0).toNat + (r1.tail.headD 0).toNat ≤ iwTop m2
      have := hg2.1; omega
    · simpa using hd2
    · simpa using ht2
  · subst hl0
    have hnil : TM.ds = [] := by
      have := decHL_length _ hds'; simpa using this
    cases n with
    | zero => simp [aplW, arfK2] at hb
    | succ n =>
    rw [show (UInt64.ofNat 0 : Word) = 0 from rfl, aplW_nil (h := rfl), arfK2_some] at hb
    cases hb
    refine ⟨.nested ids [], a, ?_, hS1, hg1, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simp only [ConRon.Arena.auxRuleFire, StateT.run_bind]
      rw [← dvl, hrun1, hnil]
      rfl
    · exact hv1d
    · exact hv1b
    · simp [decHL, hslice?]
    · simp

/-- **`aux_rule_fire` refines `auxRuleFire`** (through `view_ls` and `abstract_prefix_list`'s stub):
the fire `.nested lvls pins` as `(1, lvls, pins)`, slices below the top. -/
@[refines ConRon.Arena.auxRuleFire]
theorem auxRuleFire_refines (p : Prog) (hp : ArfLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M rP : Word) (TM : TargetMajor)
    (hS : StageR dn vis fe s₀.mem a₀) (hM : DecB (fun m => decTM m M.toNat) s₀.mem TM)
    (hP : PoolSmall s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "aux_rule_fire" [M, rP]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.auxRuleFire TM rP.toNat) a₀ ∧
      KP dn vis fe s₀.mem decFire (r, s'.mem) (AM.st (ConRon.Arena.auxRuleFire TM rP.toNat) a₀)
        (AM.res (ConRon.Arena.auxRuleFire TM rP.toNat) a₀); ⊤⦄ :=
  triple_post (auxRuleFire_spec p hp n s₀ M rP) fun _ _ ⟨hl, hw⟩ =>
    ⟨hl, (arfW_sim dn vis fe n _ a₀ M rP TM hS hM hP).am hw⟩

end L.Ind
