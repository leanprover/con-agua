import ConAgua.Arena.DeclCanonView2
import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RecGenSpec.Rec3IwSlice
import ConAgua.Arena.RecStab
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# ArfW

`ArfLook`, `auxRuleFire_spec`, `arfW`, `poolCopyW_iwFrame`, `viewLsW_iwFrame`, `decFire`.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

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
  ab : AbF p

l_model auxRuleFire_spec (p : Prog) (h : ArfLook p)
  fns [h.arf ↦ arfW]
  specs [viewLs_specW p h.ln h.alloc h.pc h.vl n,
    abstractPrefixList_spec p h.ap h.copy h.alloc h.cons h.apl h.ab n]
  grind [arena_grind] simp [rdW_eq]

theorem poolCopyW_iwFrame : ∀ (n : Nat) (m m' : Mem) (d s l : Word), poolCopyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [poolCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [poolCopyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · by_cases hs : (s &&& 1099511627775).toNat < (m.arr64 (tierA 0 (s >>> 40))).size
      · rw [poolCopyW_step n m d s l hl hs] at h
        exact (set64IW_frame _ _ _).trans (poolCopyW_iwFrame n _ _ _ _ _ h)
      · rw [poolCopyW_oob n m d s l hl (by omega)] at h; cases h

/-- `view_ls` writes only the record pool. -/
theorem viewLsW_iwFrame {n : Nat} {m m' : Mem} {us : Word} {r : List Word}
    (h : viewLsW n m us = some (r, m')) : MemFrame [IW] [200] m m' := by
  unfold viewLsW at h
  split at h; · simp at h
  split at h; · simp at h
  rename_i q m1 hal
  split at h; · simp at h
  rename_i m2 hc
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  exact (allocW_iwFrame hal).trans (poolCopyW_iwFrame _ _ _ _ _ _ hc)

/-- The fire `(1, lvls, pins)` as words. -/
def decFire (m' : Mem) (r : List Word) : IRecRuleFire → Prop
  | .nested lvls pins => r.headD 0 = 1 ∧ decRL (fun m => decHL m) 1 m' r lvls ∧
      decRL (fun m => decHL m) 3 m' r pins
  | _ => False

theorem arfW_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (M rP : Word) (TM : TargetMajor) (hS : StageR dn vis fe m a)
    (hM : DecB (fun m => decTM m M.toNat) m TM) (hP : PoolSmall m) (hA : AbsOK m) :
    RSim (arfW n m M rP) (ConRon.Arena.auxRuleFire TM rP.toNat) a
      (fun b a' x => KP dn vis fe m decFire b a' x ∧ AbsOK b.2) := by
  cases n with
  | zero => exact RSim.none
  | succ n =>
  rw [arfW.arm1]
  have hsz := hS.2.2.2.1
  have hM0 := hM.get (decTM_mono _)
  obtain ⟨-, hlv, ⟨o, l, ho, hl, hds⟩, -⟩ := rec2DecTM_parts hM0
  obtain ⟨vl, evl, hvlH, dvl⟩ := iwH_rdW_at (w := M) (k := 1) hlv hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at evl
  rw [evl]
  intro b hb
  rcases h1 : viewLsW n m vl with _ | ⟨r1, m1⟩ <;> simp only [h1, arfW.k_view_ls, reduceCtorEq] at hb
  obtain ⟨ids, hrun1, hS1, hg1, hd1, -⟩ := viewLsW_ok h1 hS hvlH hP
  have hA1 := hA.iw (viewLsW_iwFrame h1)
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
  · rcases h2 : aplW n m1 rP (UInt64.ofNat o') (UInt64.ofNat l') with _ | ⟨r2, m2⟩ <;> simp only [h2, arfW.k_abstract_prefix_list, reduceCtorEq] at hb
    cases hb
    obtain ⟨xs, a2, hrun2, hS2, hg2, hd2, ht2, hA2⟩ := aplW_ok dn vis fe n m1 m2 a rP _ _ r2 TM.ds h2 hS1 hds1
      (by rw [to, tl]; have := hS.2.1; omega) (by rw [to, tl]; have := hg1.1; omega) rP.toNat_lt hA1
    refine ⟨.nested ids xs, a2, ?_, ⟨hS2, hg1.trans hg2, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hA2⟩
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
    obtain _ | n := n
    · simp [aplW, arfW.k_abstract_prefix_list] at hb
    rw [show (UInt64.ofNat 0 : Word) = 0 from rfl, aplW.arm1 (hc1 := rfl), arfW.k_abstract_prefix_list.arm1] at hb
    cases hb
    refine ⟨.nested ids [], a, ?_, ⟨hS1, hg1, rfl, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, hA1⟩
    · simp only [ConRon.Arena.auxRuleFire, StateT.run_bind]
      rw [← dvl, hrun1, hnil]
      rfl
    · exact hv1d
    · exact hv1b
    · simp [decHL, hslice?]
    · simp

end L.Ind

end
