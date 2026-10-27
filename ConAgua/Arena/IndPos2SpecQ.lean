import ConAgua.Arena.IndPos2SpecM

/-! # `IndPos2`, the `nestPos` block (lane `indproofs2`, helper `pos2`): the representation of the
walk's data below the tops (field-kind slices, the constructors' `(kinds, closed)` records, the
fixed walk context), and the slice lemmas the block's relational proof uses. -/


noncomputable section

set_option experimental.vcgen true
open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## The walk's fixed context -/

/-- The walk's fixed context at a memory: the block's context record, the frame stack, its
`hiAt` below `2^64`. -/
structure WCtx (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (ctx po pl : Word)
    (c : NestCtx) (prog : List NestHole) : Prop where
  u : UCtx dn vis fe m ctx c
  hs : HSl m po.toNat pl.toNat prog
  hb : c.hiAt pl.toNat < 2 ^ 64

theorem WCtx.grow {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m m' : Mem} {ctx po pl : Word}
    {c : NestCtx} {prog : List NestHole} (h : WCtx dn vis fe m ctx po pl c prog) (hg : IWGrow m m') :
    WCtx dn vis fe m' ctx po pl c prog := ⟨h.u.grow hg, h.hs.grow hg, h.hb⟩

theorem WCtx.len {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {ctx po pl : Word}
    {c : NestCtx} {prog : List NestHole} (h : WCtx dn vis fe m ctx po pl c prog) : prog.length = pl.toNat :=
  h.hs.1

/-- `nest_ctx_hi_at(ctx, progLen)` is the twin's `hiAt prog.length`. -/
theorem WCtx.hi {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {ctx po pl : Word}
    {c : NestCtx} {prog : List NestHole} (h : WCtx dn vis fe m ctx po pl c prog) (htop : iwTop m < 2 ^ 64) :
    (nhiW m ctx pl).toNat = c.hiAt prog.length := by
  rw [h.len]; exact nhiW_toNat h.u.dec h.u.inn htop h.hb

/-! ## Field-kind slices, `(kinds, closed)` records -/

/-- A field-kind slice decoded below the tops. -/
def KlB (m : Mem) (o l : Nat) (ks : List NestFieldKind) : Prop := DecB (fun m => decKL m o l) m ks

theorem KlB.grow {m m' : Mem} {o l : Nat} {ks : List NestFieldKind} (h : KlB m o l ks) (hg : IWGrow m m') :
    KlB m' o l ks := DecB.grow (decKL_mono o l) hg h

theorem KlB.get {m : Mem} {o l : Nat} {ks : List NestFieldKind} (h : KlB m o l ks) : decKL m o l = some ks :=
  DecB.get (decKL_mono o l) h

theorem KlB.nil (m : Mem) (o : Nat) : KlB m o 0 [] := by simp [KlB, DecB, decKL]

theorem KlB.length {m : Mem} {o l : Nat} {ks : List NestFieldKind} (h : KlB m o l ks) : ks.length = l :=
  (decKL_get h.get).1

/-- A field-kind slice grown by one word (`sl_snoc`). -/
theorem KlB.snoc {m m' : Mem} {o l q : Nat} {ks : List NestFieldKind} {w : Word} {k : NestFieldKind}
    (h : KlB m o l ks) (_hg : IWGrow m m') (hq : q + l < iwTop m')
    (hw : ∀ i < l, (m'.arr64 IW)[q + i]? = (m.arr64 IW)[o + i]?) (hx : (m'.arr64 IW)[q + l]? = some w)
    (hk : decNFK w = some k) : KlB m' q (l + 1) (ks ++ [k]) := by
  have h' : decKL (truncM m) o l = some ks := h
  obtain ⟨hl, hg'⟩ := decKL_get h'
  show decKL (truncM m') q (l + 1) = some (ks ++ [k])
  unfold decKL
  rw [List.range_succ, List.mapM_append]
  have e1 : (List.range l).mapM (fun j => do decNFK (← (iwA (truncM m'))[q + j]?)) = some ks := by
    rw [← h']; unfold decKL
    refine mapM_congr_range _ fun j hj => ?_
    have hj' := List.mem_range.mp hj
    obtain ⟨w', hw', -⟩ := hg' j hj'
    obtain ⟨hi, -⟩ := truncM_iw_get hw'
    rw [truncM_iw_eq (m := m') (by omega), truncM_iw_eq hi]
    simp only [iwA]; rw [hw j hj']
  rw [e1]
  have e2 : (iwA (truncM m'))[q + l]? = some w := by rw [truncM_iw_eq hq]; exact hx
  simp [e2, hk]

theorem decKE_mono (v : Nat) : OMono (fun m => decKE m v) := by
  unfold decKE
  exact OMono.bind (OMono.decAt (fun o l => decKL_mono o l) v) fun _ =>
    OMono.bind (OMono.iwH (v + 2)) fun _ => OMono.const _

/-- A slice of `(kinds, closed)` records decoded below the tops. -/
def OutsB (m : Mem) (o l : Nat) (outs : List (List NestFieldKind × EIdx)) : Prop :=
  DecB (fun m => decPL m (decKE m) o l) m outs

theorem OutsB.grow {m m' : Mem} {o l : Nat} {outs : List (List NestFieldKind × EIdx)} (h : OutsB m o l outs)
    (hg : IWGrow m m') : OutsB m' o l outs := DecB.grow (OMono.decPL decKE_mono o l) hg h

theorem OutsB.nil (m : Mem) (o : Nat) : OutsB m o 0 [] := by simp [OutsB, DecB, decPL]

/-- A `(kinds, closed)` record (`rec3`). -/
theorem pos2_ke_rec {m' : Mem} {q ko kl cl : Word} {ks : List NestFieldKind} {e : EIdx}
    (hq : q.toNat + 3 ≤ iwTop m')
    (hget : ∀ j < [ko, kl, cl].length, (m'.arr64 IW)[q.toNat + j]? = [ko, kl, cl][j]?)
    (hks : KlB m' ko.toNat kl.toNat ks) (hcl : H cl) (he : decI cl = e) :
    DecB (fun m => decKE m q.toNat) m' (ks, e) := by
  have g : ∀ j < 3, (iwA (truncM m'))[q.toNat + j]? = [ko, kl, cl][j]? := fun j hj => by
    rw [truncM_iw_eq (by omega)]; exact hget j (by simpa using hj)
  have n0 : iwN (truncM m') q.toNat = some ko.toNat := by
    simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 0 (by omega))
  have n1 : iwN (truncM m') (q.toNat + 1) = some kl.toNat := by
    simpa [iwN, nat?] using congrArg (Option.map UInt64.toNat) (g 1 (by omega))
  have h2 : (iwA (truncM m'))[q.toNat + 2]? = some cl := by simpa using g 2 (by omega)
  have hks' : decKL (truncM m') ko.toNat kl.toNat = some ks := hks
  show decKE (truncM m') q.toNat = some (ks, e)
  simp only [decKE, decAt, n0, n1, hks', iwH, hd?, h2, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  simp [hcl, he]

end L.Ind
