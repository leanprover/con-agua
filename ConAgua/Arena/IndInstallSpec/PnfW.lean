module

import ConAgua.Arena.IndPosSpec.FgW
public import ConAgua.Arena.IndInstallSpec.NfsProg
public import ConAgua.Arena.IndInstallSpec.Pos3MapMProj
import ConAgua.Arena.IndPosSpec.KlB
public import ConAgua.Arena.IndPosSpec.UnW2
import ConAgua.Arena.IndSumSpec.ConsSumCtors
import ConAgua.Arena.RecClassSpec.PiBWRoom
public import ConAgua.Arena.IndInstallSpec.BlockCapsAt
public import ConAgua.Arena.IndPosSpec.NoGoStep
public import ConAgua.Arena.IndDecPLB
public import ConAgua.Arena.IndPartsSpec.PartsConsPL
import ConAgua.Arena.RecClassSpec.CloseLams

@[expose] public section

/-!
# PnfW

`decKES`, `decNFS_mono`, `decKSS_mono`, `decKES_mono`, `pos3_decAt_proj`, `pos3_kinds` and the lemmas only they use.
-/

section

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_abs_ctor_sorts_all` -/

/-- A member's normal forms: a pointer to `[off, len]` of `[k.off, k.len, e]` pointers. -/
def decKES (m : Mem) (q : Nat) : Option (List (List NestFieldKind × EIdx)) :=
  decAt m (fun o l => decPL m (decKE m) o l) q

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

theorem decNFS_mono (q : Nat) : OMono (fun m => decNFS m q) :=
  OMono.decAt (fun o l => OMono.decHL o l) q

theorem decKSS_mono (q : Nat) : OMono (fun m => decKSS m q) :=
  OMono.decAt (fun o l => OMono.decPL (fun v => OMono.decAt (fun o l => decKL_mono o l) v) o l) q

theorem decKES_mono (q : Nat) : OMono (fun m => decKES m q) :=
  OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q

theorem pos3_decAt_proj {α β : Type} {m : Mem} {g : Nat → Nat → Option (List α)}
    {g' : Nat → Nat → Option (List β)} (h : List α → List β)
    (hg : ∀ o l xs, g o l = some xs → g' o l = some (h xs)) {q : Nat} {xs : List α}
    (e : decAt m g q = some xs) : decAt m g' q = some (h xs) := by
  obtain ⟨o, l, ho, hl, hx⟩ := decAt_some e
  simp only [decAt, ho, hl, Option.bind_eq_bind, Option.bind_some]
  exact hg o l xs hx

/-- **The kinds are `outs` itself**: a `(kinds, eidx)` record read by its first two words. -/
theorem pos3_kinds {m : Mem} {o l : Nat} {outss : List (List (List NestFieldKind × EIdx))}
    (h : DecB (fun m => decPL m (decKES m) o l) m outss) :
    DecB (fun m => decPL m (decKSS m) o l) m (outss.map (·.map (·.1))) := by
  show decPL (truncM m) _ o l = _
  refine pos3_decPL_proj (List.map (·.1)) (fun v x hx => ?_) h
  refine pos3_decAt_proj (List.map (·.1)) (fun o' l' xs hxs => ?_) hx
  refine pos3_decPL_proj Prod.fst (fun w y hy => ?_) hxs
  simp only [decKE, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at hy
  obtain ⟨k, hk, e, -, rfl⟩ := hy
  exact hk

/-! ## The constructors as the positivity walk reads them (`CssAt`) -/

theorem pos3_iwN_word {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) :
    ∃ w : Word, (m.arr64 IW)[i]? = some w ∧ w.toNat = v ∧ i < iwTop m := by
  simp only [iwN, nat?, Option.map_eq_some_iff] at h
  obtain ⟨w, hw, rfl⟩ := h
  obtain ⟨hi, hw'⟩ := truncM_iw_get hw
  exact ⟨w, hw', rfl, hi⟩

/-- **`CssAt` from the constructors' decoding with bounds.** -/
theorem pos3_cssAt {m : Mem} {o l : Word} {css : List (List (IConstantVal × Nat))}
    (h : PSlR decCNSB css o l m) :
    l.toNat = css.length ∧ o.toNat + css.length ≤ iwTop m ∧ CssAt m o.toNat css := by
  have hlen : css.length = l.toNat := decPL_length _ h.dec
  refine ⟨hlen.symm, by rw [hlen]; exact h.bound, fun i hi => ?_⟩
  obtain ⟨v, hv, hcs⟩ := decPL_getH (truncM m) h.dec i (by omega)
  obtain ⟨hdr, hhdr, rfl, hi'⟩ := pos3_iwN_word hv
  obtain ⟨o', l', ho, hl, hb, hd⟩ := decCNSB_bound (m := m) (q := hdr.toNat) hcs
  obtain ⟨ow, how, rfl, hlt0⟩ := pos3_iwN_word ho
  obtain ⟨lw, hlw, rfl, hlt1⟩ := pos3_iwN_word hl
  refine ⟨hdr, ow, lw, hhdr, how, hlw, hi', hlt1, ?_, hb, fun j hj => ?_⟩
  · rw [← decPL_length _ hd]
  obtain ⟨w', hw', hx⟩ := decPL_getH (truncM m) hd j (by rw [← decPL_length _ hd]; exact hj)
  obtain ⟨w, hw, rfl, hwlt⟩ := pos3_iwN_word hw'
  refine ⟨w, hw, ?_⟩
  simp only [decCN, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at hx
  obtain ⟨q, hq, cv, hcv, nF, hnF, hx⟩ := hx
  obtain ⟨qw, hqw, rfl, hq0⟩ := pos3_iwN_word hq
  obtain ⟨nw, hnw, rfl, hq1⟩ := pos3_iwN_word hnF
  rw [← Option.some.inj hx]
  refine ⟨hq0, hq1, qw.toNat, by simp [iwN, nat?, iwA, aread_apply, hqw], decCVp_truncM hcv, by simp [iwN, nat?, iwA, aread_apply, hnw]⟩

end L.Ind

namespace L.Ind

open L.Arena

/-- `sl_cons` of a handle onto a handle slice, under the stage relation. -/
theorem pos3_consH {p : Prog} (hP : NfsProg p) {n : Nat} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List EIdx}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR vis fe m a)
    (hb : o.toNat + l.toNat ≤ iwTop m) (hx : x.toNat < 2 ^ 32) (hxs : decHL m o.toNat l.toNat = some xs) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (decI x :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat = iwTop m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ x o l) h
  obtain ⟨hS', hg, hd, ht⟩ := consW_stage hW hS hb hx hxs
  exact ⟨hS', hg, consW_mfr hW, hd, ht⟩


/-- **A `rec2` header `[off, len]` of a handle slice below the top**, decoded below the tops. -/
theorem pos3_rec2H {p : Prog} (hP : NfsProg p) {n : Nat} {vis : Word}
    {fe : IFEnv} {a : AState} {m m' : Mem} {o l : Word} {r : List Word} {xs : List EIdx}
    (h : callW p n "rec2" [o, l] m = some (r, m')) (hS : StageR vis fe m a)
    (hx : decHL m o.toNat l.toNat = some xs) (hb : o.toNat + l.toNat ≤ iwTop m) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ MFr [] [] m m' ∧ DecB (fun m => decNFS m (r.headD 0).toNat) m' xs := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h
  obtain ⟨-, -, -, hf, -, -⟩ := recW_post hW hS.iw.ctl hS.iw.iwSize rfl
  obtain ⟨hS', hg, hr, hget, htop⟩ := recW_stage hW hS rfl
  refine ⟨hS', hg, MFr.of_iw hf, ?_⟩
  subst hr
  have hq0 : (rdW (m.arr64 CTL) 200).toNat < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m.arr64 CTL) 200).toNat + 1 < iwTop s'.mem := by rw [htop]; simp [iwTop]
  have w0 : iwN (truncM s'.mem) (rdW (m.arr64 CTL) 200).toNat = some o.toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, aread_apply, this]
  have w1 : iwN (truncM s'.mem) ((rdW (m.arr64 CTL) 200).toNat + 1) = some l.toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, aread_apply, this]
  have hd := (decHL_decB hx hb).grow (OMono.decHL _ _) hg
  show decAt (truncM s'.mem) _ _ = some xs
  simp only [decAt, List.headD_cons, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hd


end L.Ind

end
