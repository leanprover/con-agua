module

public import ConAgua.Arena.IndInstallSpec.DecCNS
public import ConAgua.Arena.IndInstallSpec.DecISS
import ConAgua.Arena.IndInstallSpec.Pos3MapMProj
import ConAgua.Arena.RecClassSpec.PiBWRoom
public import ConAgua.Arena.IndDecPLB

@[expose] public section

/-!
# InstallRec2PSl

`decIS_mono`, `decISS_mono` and the lemmas only they use.
-/

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem decIS_mono (q : Nat) : OMono (fun m => decIS m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

end L.Ind

end

end

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem decISS_mono (q : Nat) : OMono (fun m => decISS m q) :=
  OMono.decAt (fun o l => OMono.decPL decIS_mono o l) q

/-- With the bound dropped. -/
theorem decCNSB_decCNS {m : Mem} {q : Nat} {cs : List (IConstantVal × Nat)}
    (h : DecB (fun m => decCNSB m q) m cs) : DecB (fun m => decCNS m q) m cs := by
  obtain ⟨o, l, ho, hl, -, hd⟩ := decCNSB_bound h
  show decAt (truncM m) _ q = some cs
  simp only [decAt, ho, hl, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **A `rec2` header `[off, len]` of a slice decoded below the tops**, decoded below the tops. -/
theorem installRec2PSl {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (hW : recW m 2 [o, l] = some (r, m')) (hS : StageR vis fe m a) (hx : PSlR f xs o l m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decAt m (fun o l => decPL m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  refine ⟨hS', hg, ?_⟩
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop m' := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop m' := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM m') (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, aread_apply, this]
  have w1 : iwN (truncM m') ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, aread_apply, this]
  have hd := hx.dec.grow (OMono.decPL hf _ _) hg
  show decAt (truncM m') _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **A `rec2` header `[off, len]` of a slice below the tops**, decoded with its bound. -/
theorem installRec2PSlB {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (hW : recW m 2 [o, l] = some (r, m')) (hS : StageR vis fe m a) (hx : PSlR f xs o l m) :
    DecB (fun m => decAt m (fun o l => decPLB m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop m' := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop m' := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM m') (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, aread_apply, this]
  have w1 : iwN (truncM m') ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, aread_apply, this]
  have hd := hx.dec.grow (OMono.decPL hf _ _) hg
  show decAt (truncM m') _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some, decPLB]
  rw [ite_eq_left (le_iwA_truncM_size (Nat.le_trans hx.bound hg.iw) hS'.iw.1)]
  exact hd

theorem lpsW_afr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    by_cases hz : rdW (m.arr64 IW) (q + 1) = 0
    · rw [lpsW_nil n m q hz] at h; obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h); exact AFr.refl _
    · rw [lpsW_cons n m q hz] at h; exact erToIwW_afr h

end L.Ind

end

end

section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The constructors, read by `check_abs_ctor_sorts_all`. -/
theorem pos3_cns {m : Mem} {o l : Word} {css : List (List (IConstantVal × Nat))}
    (h : PSlR decCNSB css o l m) : PSlR0 decCNS css o l m := by
  refine ⟨?_, Or.inr h.bound⟩
  show decPL (truncM m) _ o.toNat l.toNat = some css
  have := pos3_decPL_proj (m := truncM m) (g := decCNS (truncM m)) id
    (fun v x hx => decCNSB_decCNS (m := m) (q := v) hx) h.dec
  rwa [List.map_id] at this

end L.Ind

end

