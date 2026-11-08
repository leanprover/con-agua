module

public import ConAgua.Arena.DeclCanonView2
public import ConAgua.Arena.RecCheckSpec.ErToIwWStage
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RecGenSpec.Rec3IwSlice
import ConAgua.Arena.RecStab
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Arena.IndInstallSpec.DomsW
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.IndDecStab
public import ConAgua.Arena.RecSim
import all ConAgua.Arena.RecCheck

@[expose] public section

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
  grind [arena_grind]

theorem poolCopyW_iwFrame : ∀ (n : Nat) (m m' : Mem) (d s l : Word), poolCopyW n m d s l = some m' →
    MemFrame [IW] [200] m m'
  | 0, _, _, _, _, _, h => by simp [poolCopyW] at h
  | n + 1, m, m', d, s, l, h => by
    by_cases hl : l = 0
    · rw [poolCopyW_nil n m d s l hl] at h; cases h; exact MemFrame.refl _ _ _
    · by_cases hs : (s &&& 1099511627775).toNat < (m.arr64 (tierA POOL (s >>> 40))).size
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
    (a : AState) (M rP : Word) (TM : TargetMajor) (hS : StageR vis fe m a)
    (hM : DecB (fun m => decTM m M.toNat) m TM) (hP : PoolSmall m) (hA : AbsOK m) :
    RSim (arfW n m M rP) (ConRon.Arena.auxRuleFire TM rP.toNat) a
      (fun b a' x => KP dn vis fe m decFire b a' x ∧ AbsOK b.2) := by
  sorry

end L.Ind

end
