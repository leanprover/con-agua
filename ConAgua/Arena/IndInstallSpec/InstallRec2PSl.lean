import ConAgua.Arena.IndInstallSpec.DecCNS
import ConAgua.Arena.IndInstallSpec.DecISS
import ConAgua.Arena.IndInstallSpec.Pos3MapMProj

/-!
# InstallRec2PSl

`decIS_mono`, `decISS_mono`, `iwA_size_mono`, `decPLB_omono`, `decCNSB_mono`, `le_iwA_truncM_size` and the lemmas only they use.
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

theorem iwA_size_mono {m m' : Mem} (he : PoolExt m m') : (iwA m).size ≤ (iwA m').size := by
  rcases Nat.eq_zero_or_pos (iwA m).size with h0 | h0
  · omega
  · have h1 : (iwA m)[(iwA m).size - 1]? = some ((iwA m)[(iwA m).size - 1]'(by omega)) :=
      Array.getElem?_eq_getElem _
    have := (Array.getElem?_eq_some_iff.mp (he.1 _ _ h1)).1
    omega

theorem decPLB_omono {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q)) (o l : Nat) :
    OMono (fun m => decPLB m (f m) o l) := by
  refine ⟨fun m m' x he h => ?_⟩
  simp only [decPLB] at h ⊢
  split at h
  · rename_i hb
    rw [ite_eq_left (Nat.le_trans hb (iwA_size_mono he))]
    exact (OMono.decPL hf o l).mono m m' x he h
  · cases h

theorem decCNSB_mono (q : Nat) : OMono (fun m => decCNSB m q) :=
  OMono.decAt (fun o l => decPLB_omono decCN_mono o l) q

/-- … and at least every bound below the top, when the top lies within the pool. -/
theorem le_iwA_truncM_size {m : Mem} {k : Nat} (hk : k ≤ iwTop m) (hT : iwTop m ≤ (iwA m).size) :
    k ≤ (iwA (truncM m)).size := by
  rcases Nat.eq_zero_or_pos k with h0 | h0
  · omega
  · have e := truncM_iw_get? m (k - 1)
    rw [ite_eq_left (by omega), Array.getElem?_eq_getElem (show k - 1 < (iwA m).size by omega)] at e
    have := (Array.getElem?_eq_some_iff.mp e).1
    omega

/-- With the bound dropped. -/
theorem decCNSB_decCNS {m : Mem} {q : Nat} {cs : List (IConstantVal × Nat)}
    (h : DecB (fun m => decCNSB m q) m cs) : DecB (fun m => decCNS m q) m cs := by
  obtain ⟨o, l, ho, hl, -, hd⟩ := decCNSB_bound h
  show decAt (truncM m) _ q = some cs
  simp only [decAt, ho, hl, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **A `rec2` header `[off, len]` of a slice decoded below the tops**, decoded below the tops. -/
theorem installRec2PSl {p : Prog} (hP : CtorsProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR f xs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      DecB (fun m => decAt m (fun o l => decPL m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  refine ⟨hS', hg, ?_⟩
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hd := hx.1.grow (OMono.decPL hf _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hd

/-- **A `rec2` header `[off, len]` of a slice below the tops**, decoded with its bound. -/
theorem installRec2PSlB {p : Prog} (hP : CtorsProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List α}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR dn vis fe m a) (hx : PSlR f xs o l m) :
    DecB (fun m => decAt m (fun o l => decPLB m (f m) o l) (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hd := hx.1.grow (OMono.decPL hf _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some, decPLB]
  rw [ite_eq_left (le_iwA_truncM_size (Nat.le_trans hx.2 hg.1) hS'.2.1)]
  exact hd

theorem lpsW_afr {n : Nat} {m m' : Mem} {q : Word} {r : List Word} (h : lpsW n m q = some (r, m')) :
    AFr m m' := by
  cases n with
  | zero => simp [lpsW] at h
  | succ n =>
    simp only [lpsW] at h
    afr_auto h [erToIwW_afr]

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
  refine ⟨?_, Or.inr h.2⟩
  show decPL (truncM m) _ o.toNat l.toNat = some css
  have := pos3_decPL_proj (m := truncM m) (g := decCNS (truncM m)) id
    (fun v x hx => decCNSB_decCNS (m := m) (q := v) hx) h.1
  rwa [List.map_id] at this

end L.Ind

end
