module

public import ConAgua.Arena.IndSumSpec.ColW
public import ConAgua.Arena.IndSumSpec.StructProjArgP
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndGrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.IndMaster
import ConRon.Bridge.Grind
import Std.Tactic.BVDecide.Normalize.BitVec
import all ConAgua.Arena.IndSum

@[expose] public section

/-!
# Row: `ConRon.Arena.paramLevels.go`

The refinement theorem `paramLevelsGo_refines`, the `struct_ps_at` stage lemmas and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

section arms
variable (k : Nat) (m m1 m2 m3 : Mem) (o l u q : Word) (r : List Word)
theorem plK2_some : plK2 k u (some (r, m2)) = plK3 (consW k m2 u (r.headD 0) (r.tail.headD 0)) := rfl
theorem plK3_some : plK3 (some (r, m3)) = some ([r.headD 0, r.tail.headD 0], m3) := rfl
end arms

grind_pattern [ind_grind] plK2_some => plK2 k u (some (r, m2))
grind_pattern [ind_grind] plK3_some => plK3 (some (r, m3))

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hp : p.lookup "param_levels_go" = some paramLevelsGoL)
include ha hc hsc hg hpf hpp hip hp

theorem plgW_spec (k : Nat) : ∀ (s₀ : St) (o l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels_go" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ plgW k s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  induction k with
  | zero =>
    intro s₀ o l; rw [invoke_eq _ hp]; simp only [callFn, paramLevelsGoL]
    vcgen [exec] <;> grind
  | succ k ih =>
    intro s₀ o l
    rw [invoke_eq _ hp]
    simp only [callFn, paramLevelsGoL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        iwAlloc_specW p ha k, slGet_specW p hg k, internParam_spec p hpf hpp hip k,
        slCons_specW p ha hc hsc k, ih] <;>
      finish (gen := 20) [getW]

end spec

theorem plgW_ok (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (k : Nat) :
    ∀ (m m' : Mem) (a : AState) (o l : Word) (lps : List NIdx) (r : List Word),
    plgW k m o l = some (r, m') → StageR vis fe m a → decHL m o.toNat l.toNat = some lps →
    o.toNat + l.toNat < 2 ^ 64 → o.toNat + l.toNat ≤ iwTop m →
    ∃ us a', (paramLevels.go lps).run a = .ok (us, a') ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some us ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  induction k with
  | zero => intro m m' a o l lps r h; simp [plgW] at h
  | succ k ih =>
    intro m m' a o l lps r h hS hd hb ht
    by_cases hl : l = 0
    · subst hl
      rw [plgW_nil k m o 0 rfl] at h
      obtain ⟨q, m1, h0, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK0_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hq, htop⟩ := allocW_stage h0 hS
      have : lps = [] := by simpa [decHL, hslice?] using hd.symm
      subst this
      exact ⟨[], a, rfl, hS1, hg1, by simp [decHL, hslice?], by simp [htop, hq]⟩
    · obtain ⟨w, lps', rfl, hw, hw32, hd'⟩ := decHL_cons hd hl hb
      obtain ⟨hsum, -⟩ := toNat_succ_of_lt hb hl
      rw [plgW_cons k m o l hl, hw] at h
      obtain ⟨u, m1, h1, h⟩ := kSome_inv h (by simp [plK1]) (fun _ _ => rfl)
      by_cases hu : 4294967296 ≤ u
      · rw [plK1_big k m1 o l u hu] at h; cases h
      rw [plK1_ok k m1 o l u hu] at h
      have hu32 : u.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ u.toNat := hu; omega
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internParam_stage hS w hw32 h1
      obtain ⟨r2, m2, h2, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK2_some] at h
      obtain ⟨us, a2, hrun2, hS2, hg2, hd2, ht2⟩ := ih m1 m2 a1 (o + 1) (l - 1) lps' r2 h2 hS1
        (by rw [decHL_grow hg1 (by omega)]; exact hd') (by omega) (by have := hg1.iw; omega)
      obtain ⟨r3, m3, h3, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [plK3_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage h3 hS2 (Nat.le_of_eq ht2) hu32 hd2
      refine ⟨decI u :: us, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa using hd3, by simpa using ht3⟩
      simp only [paramLevels.go, StateT.run_bind, hrun1]
      simp only [bind, Except.bind, hrun2]
      rfl

section census
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
  (hc : p.lookup "iw_copy" = some iwCopy) (hsc : p.lookup "sl_cons" = some slCons)
  (hg : p.lookup "sl_get" = some slGet)
  (hpf : p.lookup "param_find" = some paramFind) (hpp : p.lookup "param_push" = some paramPush)
  (hip : p.lookup "intern_param" = some internParam)
  (hp : p.lookup "param_levels_go" = some paramLevelsGoL)
include ha hc hsc hg hpf hpp hip hp

/-- **`param_levels_go` refines `paramLevels.go`** under the stage relation. -/
@[refines ConRon.Arena.paramLevels.go]
theorem paramLevelsGo_refines (k : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (o l : Word) (lps : List NIdx) (hS : StageR vis fe s₀.mem a₀)
    (hd : decHL s₀.mem o.toNat l.toNat = some lps) (hb : o.toNat + l.toNat < 2 ^ 64)
    (ht : o.toNat + l.toNat ≤ iwTop s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels_go" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (paramLevels.go lps) a₀ ∧
      StageR vis fe s'.mem (AM.st (paramLevels.go lps) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      decHL s'.mem (r.headD 0).toNat (r.tail.headD 0).toNat = some (AM.res (paramLevels.go lps) a₀) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop s'.mem; ⊤⦄ := by
  refine triple_post (plgW_spec p ha hc hsc hg hpf hpp hip hp k s₀ o l) ?_
  rintro r s' ⟨hl, hm⟩
  obtain ⟨us, a', hrun, hS', hg', hd', ht'⟩ := plgW_ok dn vis fe k _ _ _ _ _ _ _ hm hS hd hb ht
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, by rw [hst]; exact hS', hg', by rw [hres]; exact hd', ht'⟩

theorem plW_spec (hq : p.lookup "param_levels" = some paramLevelsL) (hil : IlF p) (k : Nat) (s₀ : St) (o l : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p k) "param_levels" [o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ plW k s₀.mem o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hq]
  simp only [callFn, paramLevelsL]
  cases k with
  | zero => vcgen [exec] <;> grind
  | succ k =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
        plgW_spec p ha hc hsc hg hpf hpp hip hp k, ilF_spec p hil k] <;>
      finish

end census

end L.Ind

namespace L.Ind

open L.Arena

/-! ## `struct_ps_at` under the stage relation -/

theorem psGoW_stage (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) :
    ∀ (m m' : Mem) (a : AState) (o nP N k : Word) (r : List Word),
    psGoW n m o nP N k = some (r, m') → StageR vis fe m a →
    o.toNat + nP.toNat < 2 ^ 64 → k.toNat + N.toNat ≤ nP.toNat →
    ∃ xs a', (structPsAt.go o.toNat nP.toNat N.toNat k.toNat).run a = .ok (xs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  induction n with
  | zero => intro m m' a o nP N k r h; simp [psGoW] at h
  | succ n ih =>
    intro m m' a o nP N k r h hS hon hkN
    by_cases hN : N = 0
    · subst hN
      rw [psGoW_nil n m o nP 0 k rfl] at h
      obtain ⟨q, m1, h0, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [psK0_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS1, hg1, hq, htop⟩ := allocW_stage h0 hS
      exact ⟨[], a, by simp [structPsAt.go]; rfl, hS1, hg1, by simp [decHL, hslice?], by simp [htop, hq]⟩
    · rw [psGoW_cons n m o nP N k hN] at h
      obtain ⟨b, m1, hI, h⟩ := kSome_inv h (by simp [psK1]) (fun _ _ => rfl)
      by_cases hb : 4294967296 ≤ b
      · rw [psK1_big n m1 o nP N k b hb] at h; simp at h
      rw [psK1_ok n m1 o nP N k b hb] at h
      have hb32 : b.toNat < 2 ^ 32 := by have : ¬ (4294967296 : Nat) ≤ b.toNat := hb; omega
      have hN1 : 1 ≤ N.toNat := by
        have : N.toNat ≠ 0 := fun h0 => hN (UInt64.toNat_inj.mp (by simpa using h0))
        omega
      obtain ⟨a1, hrun1, hS1, hg1⟩ := internBVar_stage hS _ hI
      obtain ⟨r2, m2, hr, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [psK2_some] at h
      have hk1 : (k + 1).toNat = k.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hN1' : (N - 1).toNat = N.toNat - 1 := by rw [UInt64.toNat_sub]; simp; omega
      obtain ⟨xs, a2, hrun2, hS2, hg2, hd2, ht2⟩ :=
        ih m1 m2 a1 o nP (N - 1) (k + 1) r2 hr hS1 hon (by rw [hk1, hN1']; omega)
      obtain ⟨r3, m3, hcw, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
      rw [psK3_some] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      obtain ⟨hS3, hg3, hd3, ht3⟩ := consW_stage hcw hS2 (Nat.le_of_eq ht2) hb32 hd2
      refine ⟨decE b :: xs, a2, ?_, hS3, (hg1.trans hg2).trans hg3, by simpa [decE_eq] using hd3,
        by simpa using ht3⟩
      have hu : (o + nP - 1 - k).toNat = o.toNat + nP.toNat - 1 - k.toNat := by
        rw [UInt64.toNat_sub, UInt64.toNat_sub, UInt64.toNat_add]; simp; omega
      have hNs : N.toNat = (N.toNat - 1) + 1 := by omega
      rw [hNs]
      simp only [structPsAt.go]
      rw [StateT.run_bind, ← hu, hrun1]
      simp only [bind, Except.bind]
      rw [← hk1, ← hN1']
      simp only [StateT.run] at hrun2
      simp only [StateT.bind, StateT.run, hrun2]
      rfl

theorem psAtW_stage (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat)
    (m m' : Mem) (a : AState) (o nP : Word) (r : List Word)
    (h : psAtW n m o nP = some (r, m')) (hS : StageR vis fe m a) (hon : o.toNat + nP.toNat < 2 ^ 64) :
    ∃ xs a', (structPsAt o.toNat nP.toNat).run a = .ok (xs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some xs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  cases n with
  | zero => cases h
  | succ n =>
    rw [psAtW_succ] at h
    obtain ⟨r0, m0, hg, h⟩ := kSome_inv h rfl (fun _ _ => rfl)
    rw [psK3_some] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    obtain ⟨xs, a', hrun, hS', hgr, hd, ht⟩ := psGoW_stage dn vis fe n m m0 a o nP nP 0 r0 hg hS hon (by simp)
    exact ⟨xs, a', by simpa [structPsAt] using hrun, hS', hgr, by simpa using hd, by simpa using ht⟩

end L.Ind

end
