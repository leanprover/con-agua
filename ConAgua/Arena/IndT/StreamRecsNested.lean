module

public import ConAgua.Arena.IndT.StreamRecsTop
public import ConAgua.Arena.IndT.SumSteps
import ConAgua.Arena.DefEqMidPeel
import ConAgua.Arena.IndPartsSpec.RecTW
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndInstallSpec.DomsW
import ConAgua.Arena.RecCheckSpec.ArfW
import ConAgua.Arena.IndSumSpec.TsrW
import ConAgua.Arena.IndRealMemo
import ConAgua.Arena.StageInst1
import ConAgua.L.ModelGen
import ConRon.Bridge.Inductives.StreamRecs
import all ConAgua.Arena.IndStream

@[expose] public section

/-!
# `stream_nested_ok` under `StageC` (lane `ronsync2`, stage 3)

`stream_nested_ok(ty, mI, rP, kind, lvls, pins)` (`IndStream.lean`) and its helpers
`stream_nested_dom`, `stream_nested_pins`, `stream_nested_bvars`: their models (`snoW`, `sndW`,
`snpW`, `snbW`, callees through their runs `callW`), the callees' steps under the stage relation
(`StageR`, `AbsOK`, the `IW` growth), the helpers' sims against con-ron's `streamNestedDom` and
its two `mapM`s, and `snoSim_of : SnoProg p → SnoSim p dn`, the obligation `sr1_ref` takes (the
twin's step from con-ron's `streamNestedOk_run`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

/-- The lookups `stream_nested_ok` needs. -/
structure SnoProg (p : Prog) : Prop where
  ok : p.lookup "stream_nested_ok" = some streamNestedOkL
  dom : p.lookup "stream_nested_dom" = some streamNestedDomL
  pins : p.lookup "stream_nested_pins" = some streamNestedPins
  bvars : p.lookup "stream_nested_bvars" = some streamNestedBvars
  ev : p.lookup "e_view" = some eView
  ln : p.lookup "ls_node" = some lsNode
  pc : p.lookup "pool_copy" = some poolCopy
  vl : p.lookup "view_ls" = some viewLsL
  app : p.lookup "sl_append" = some slAppend
  le : p.lookup "lift_entry" = some liftEntry
  lift : LiftProg p
  sum : SumProg p

l_model snpW_spec (p : Prog) (h : SnoProg p)
  fns [h.pins ↦ snpW]
  specs [callW_spec p n "lift_entry", callW_spec p n "sl_cons"]
  grind [arena_grind] extra [ld64_rd_spec]

l_model snbW_spec (p : Prog) (h : SnoProg p)
  fns [h.bvars ↦ snbW]
  specs [callW_spec p n "intern_bvar", callW_spec p n "sl_cons"]
  grind [arena_grind]

l_model sndW_spec (p : Prog) (h : SnoProg p)
  fns [h.dom ↦ sndW]
  specs [callW_spec p n "get_app_fn_f", callW_spec p n "e_view", callW_spec p n "view_ls",
    callW_spec p n "sl_eq", callW_spec p n "get_app_args_f", callW_spec p n "stream_nested_pins",
    callW_spec p n "stream_nested_bvars", callW_spec p n "sl_append"]
  grind [arena_grind] extra [evalE_tagE]

l_model snoW_spec (p : Prog) (h : SnoProg p)
  fns [h.ok ↦ snoW]
  specs [callW_spec p n "strip_pis", callW_spec p n "e_view", callW_spec p n "stream_nested_dom"]
  grind [arena_grind] extra [evalE_tagE]

/-! ## The callees' steps under the stage relation -/

section steps
variable {p : Prog} {vis : Word} {fe : IFEnv}

theorem liftA_tier : ∀ b ∈ liftA, InStoreTier b := by simp only [liftA]; decide

theorem liftC_lt : ∀ x ∈ liftC, x.toNat < 64 := by
  intro x hx; simp only [liftC, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide

/-- **`lift_entry` returns a handle word** (below `2^32`). Not proved here: the walk returns its
input, an interned node or a memo hit, unmasked (`LiftL.lean`), and the lift memo's relation
(`ArenaD`, `MemoRG decE`) does not bound its value words; `inst_entry` and `abs_entry` mask
their result (`& 4294967295`) for this. Needs the core area (a bound in `liftEntry_refines`, or
the mask in `lift_entry`), or a guard `if 4294967296 <= x { abort }` in `stream_nested_pins` as
`stream_nested_bvars` has. -/
theorem liftEntry_hw {n : Nat} {m m' : Mem} {a : AState} {h k c f : Word} {r : List Word}
    (hS : StageR vis fe m a) (hh : H h)
    (hc : callW p n "lift_entry" [h, k, c, f] m = some (r, m')) : H (r.headD 0) := by
  sorry

/-- **`lift_entry`'s step**: con-ron's `liftLooseBVarsFast` at the core walk fuel, the stage
relation, the growth and the memos after. -/
theorem lift_step (hL : LiftProg p) (he : p.lookup "lift_entry" = some liftEntry) {n : Nat}
    {m m' : Mem} {a : AState} {h k : Word} {r : List Word} (hS : StageR vis fe m a) (hA : AbsOK m)
    (hh : H h) (hc : callW p n "lift_entry" [h, k, 0, CWF] m = some (r, m')) :
    ∃ a', (liftLooseBVarsFast coreWalkFuel k.toNat 0 (decI h)).run a = .ok (decI (r.headD 0), a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ H (r.headD 0) := by
  have hfr : MemFrame liftA liftC m m' :=
    (run_memFrame (hL.closed he) (by decide) (run_of_callW hc)).1
  rcases n with _ | n
  · rw [callW_zero] at hc; cases hc
  obtain ⟨s', hs', -, hok, hD, hres⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (liftEntry_refines p hL he n _ a hS.check.arena h k 0 CWF hh) hc
  rw [hs'] at hD
  have hrun := AM.run_of_ok _ a hok
  rw [CWF_eq] at hrun hD hres
  have hcp := (keeps_liftFast _ _ _ _).run hrun
  obtain ⟨hS', hg⟩ := StageR.of_walk hS hD hfr liftA_tier liftC_lt hcp
  refine ⟨_, ?_, hS', hg, AFr.of_frame hfr (by decide) (by decide) hA, liftEntry_hw hS hh hc⟩
  show (liftLooseBVarsFast coreWalkFuel k.toNat (UInt64.toNat 0) (decE h)).run a =
    .ok (decE (r.headD 0), _)
  rw [hrun, hres]

/-- **`intern_bvar`'s step**. -/
theorem bvar_step (hP : SumProg p) {n : Nat} {m m' : Mem} {a : AState} {u : Word} {r : List Word}
    (hS : StageR vis fe m a) (hA : AbsOK m) (hc : callW p n "intern_bvar" [u] m = some (r, m')) :
    ∃ a', (internBVarE u.toNat).run a = .ok (decI (r.headD 0), a') ∧ StageR vis fe m' a' ∧
      IWGrow m m' ∧ AbsOK m' := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internBVar_spec (p := p) hP.hbf hP.hbp hP.hib n _ u) hc
  obtain ⟨a', hrun, hS', hg⟩ := internBVar_stage hS u hm
  exact ⟨a', hrun, hS', hg, binternW_afr hm hA⟩

/-- **`sl_cons`'s step** (no twin step). -/
theorem cons_step (hP : SumProg p) {n : Nat} {m m' : Mem} {a : AState} {x o l : Word} {r : List Word}
    {k : IdxKind} {xs : List (Idx k)} (hS : StageR vis fe m a) (hA : AbsOK m)
    (hb : o.toNat + l.toNat ≤ iwTop m) (hx : H x) (hxs : decHL m o.toNat l.toNat = some xs)
    (hc : callW p n "sl_cons" [x, o, l] m = some (r, m')) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ AbsOK m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (decI x :: xs) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.ha hP.hc hP.hsc n _ x o l) hc
  obtain ⟨hS', hg, hd, ht⟩ := consW_stage hm hS hb hx hxs
  exact ⟨hS', hg, hA.consW hm, hd, Nat.le_of_eq ht⟩

/-- **`sl_append`'s step** (no twin step). -/
theorem append_step (hP : SumProg p) (happ : p.lookup "sl_append" = some slAppend) {n : Nat}
    {m m' : Mem} {a : AState} {o1 l1 o2 l2 : Word} {r : List Word} {xs ys : List EIdx}
    (hS : StageR vis fe m a) (hA : AbsOK m) (hb1 : o1.toNat + l1.toNat ≤ iwTop m)
    (hb2 : o2.toNat + l2.toNat ≤ iwTop m) (hxs : decHL m o1.toNat l1.toNat = some xs)
    (hys : decHL m o2.toNat l2.toNat = some ys)
    (hc : callW p n "sl_append" [o1, l1, o2, l2] m = some (r, m')) :
    StageR vis fe m' a ∧ IWGrow m m' ∧ AbsOK m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some (xs ++ ys) ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slAppend_specW p hP.ha hP.hc happ n _ o1 l1 o2 l2) hc
  obtain ⟨hS', hg, -⟩ := appendW_stage hm hS hb1 hb2
  obtain ⟨rfl, hd, -, -, -, ht⟩ := appendW_dec hm hS.iw.iwSize hS.iw.ctl hb1 hb2 hxs hys
  exact ⟨hS', hg, appendW_afr hm hA, hd, Nat.le_of_eq ht⟩

/-- **`sl_eq`** at any handle kind: the memory unchanged, `0` exactly when the slices differ. -/
theorem slEq_stepK (hP : SumProg p) {n : Nat} {m m' : Mem} {a : AState} {o1 l1 o2 l2 : Word}
    {k : IdxKind} {xs ys : List (Idx k)} (hS : StageR vis fe m a)
    (h1 : decHL m o1.toNat l1.toNat = some xs) (hb1 : o1.toNat + l1.toNat ≤ iwTop m)
    (h2 : decHL m o2.toNat l2.toNat = some ys) (hb2 : o2.toNat + l2.toNat ≤ iwTop m) {r : List Word}
    (hc : callW p n "sl_eq" [o1, l1, o2, l2] m = some (r, m')) :
    m' = m ∧ (r.headD 0 = 0 ↔ xs ≠ ys) := by
  obtain ⟨s, hs, -, hm, hq⟩ := triple_of_callW (slEq_spec p hP.heq n ⟨m, Locals.init []⟩ o1 l1 o2 l2) hc
  obtain ⟨ws1, hs1, hmm1, hw1⟩ := slR_of_decHL m _ _ _ h1 (hS.lt64 hb1)
  obtain ⟨ws2, hs2, hmm2, hw2⟩ := slR_of_decHL m _ _ _ h2 (hS.lt64 hb2)
  simp only [UInt64.ofNat_toNat] at hs1 hs2
  have heq := eqW_ok n m _ _ _ _ (r.headD 0) ws1 ws2 hs1 hs2 hq
  refine ⟨by rw [← hs, hm], ?_⟩
  rw [heq, hmm1, hmm2, Ne, map_decI_inj ws1 ws2 hw1 hw2]
  by_cases hw : ws1 = ws2 <;> simp [hw]

end steps

/-! ## `stream_nested_pins` and `stream_nested_bvars`: the twin's two `mapM`s -/

section lists
variable {p : Prog} {vis : Word} {fe : IFEnv}

/-- **`stream_nested_pins`' model is the pins lifted** (`pins.mapM liftLooseBVarsFast`). -/
theorem snpW_ok (h : SnoProg p) (k : Word) : ∀ (N : Nat) (m m' : Mem) (a : AState) (po pl : Word)
    (pins : List EIdx) (r : List Word),
    snpW p N m k po pl = some (r, m') → StageR vis fe m a → AbsOK m →
    decHL m po.toNat pl.toNat = some pins → po.toNat + pl.toNat ≤ iwTop m →
    ∃ ps a', (pins.mapM (liftLooseBVarsFast coreWalkFuel k.toNat 0)).run a = .ok (ps, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ps ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro N
  induction N with
  | zero => intro m m' a po pl pins r hc; rw [snpW.eq_1] at hc; cases hc
  | succ N ih =>
    intro m m' a po pl pins r hc hS hA hd hb
    by_cases hl : pl = 0
    · rw [snpW.arm1 p N m k po pl hl] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      have hz : pl.toNat = 0 := by rw [hl]; rfl
      rw [hz] at hd
      simp only [decHL, hslice?, List.range_zero, List.mapM_nil, Option.pure_def,
        Option.some.injEq] at hd
      subst hd
      exact ⟨[], a, rfl, hS, IWGrow.refl m, hA, by simp [decHL, hslice?], by simp⟩
    rw [snpW.arm2 p N m k po pl hl] at hc
    obtain ⟨x, xs', w, rfl, hxs', hw1, hw2, hw3, hpo1, hpl1⟩ := rcSl_step hd hl (hS.lt64 hb)
    rw [hw1] at hc
    rcases h1 : callW p N "lift_entry" [w, k, 0, CWF] m with _ | ⟨r1, m1⟩ <;>
      rw [h1] at hc
    · rw [snpW.k_lift_entry.none] at hc; cases hc
    rw [snpW.k_lift_entry.arm1] at hc
    obtain ⟨a1, hrun1, hS1, hg1, hA1, hH1⟩ := lift_step h.lift h.le hS hA hw2 h1
    rcases h2 : snpW p N m1 k (po + 1) (pl - 1) with _ | ⟨r2, m2⟩ <;> rw [h2] at hc
    · rw [snpW.k_stream_nested_pins.none] at hc; cases hc
    rw [snpW.k_stream_nested_pins.arm1] at hc
    have hd1 : decHL m1 (po + 1).toNat (pl - 1).toNat = some xs' := by
      rw [decHL_grow hg1 (by omega)]; exact hxs'
    obtain ⟨ps2, a2, hrun2, hS2, hg2, hA2, hd2, ht2⟩ :=
      ih m1 m2 a1 (po + 1) (pl - 1) xs' r2 h2 hS1 hA1 hd1 (by have := hg1.iw; omega)
    rcases h3 : callW p N "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
      rw [h3] at hc
    · rw [snpW.k_sl_cons.none] at hc; cases hc
    rw [snpW.k_sl_cons.arm1] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    obtain ⟨hS3, hg3, hA3, hd3, ht3⟩ := cons_step h.sum hS2 hA2 ht2 hH1 hd2 h3
    refine ⟨decI (r1.headD 0) :: ps2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, hA3,
      by simpa using hd3, by simpa using ht3⟩
    simp only [List.mapM_cons, StateT.run_bind, ← hw3, hrun1, except_ok_bind, hrun2]
    rfl

/-- **`stream_nested_bvars`' model is the index variables** (`internBVarE (n - 1 - j)` for
`j = i, …, n - 1`). -/
theorem snbW_ok (h : SnoProg p) (k : Word) : ∀ (N : Nat) (m m' : Mem) (a : AState) (i : Word)
    (r : List Word),
    snbW p N m k i = some (r, m') → StageR vis fe m a → AbsOK m →
    ∃ bs a', ((List.range' i.toNat (k.toNat - i.toNat)).mapM
        (fun j => internBVarE (k.toNat - 1 - j))).run a = .ok (bs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  intro N
  induction N with
  | zero => intro m m' a i r hc; rw [snbW.eq_1] at hc; cases hc
  | succ N ih =>
    intro m m' a i r hc hS hA
    by_cases hl : k ≤ i
    · rw [snbW.arm1 p N m k i hl] at hc
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      have hz : k.toNat - i.toNat = 0 := by have := UInt64.le_iff_toNat_le.mp hl; omega
      rw [hz]
      exact ⟨[], a, rfl, hS, IWGrow.refl m, hA, by simp [decHL, hslice?], by simp⟩
    rw [snbW.arm2 p N m k i hl] at hc
    have hlt : i.toNat < k.toNat := Nat.lt_of_not_le (fun h' => hl (UInt64.le_iff_toNat_le.mpr h'))
    have hu : (k - 1 - i).toNat = k.toNat - 1 - i.toNat := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega)),
        UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
    have hi1 : (i + 1).toNat = i.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := UInt64.toNat_lt k; omega
    rcases h1 : callW p N "intern_bvar" [k - 1 - i] m with _ | ⟨r1, m1⟩ <;> rw [h1] at hc
    · rw [snbW.k_intern_bvar.none] at hc; cases hc
    by_cases hbig : 4294967296 ≤ r1.headD 0
    · rw [snbW.k_intern_bvar.abort1 _ _ _ _ _ _ hbig] at hc; cases hc
    rw [snbW.k_intern_bvar.arm1 _ _ _ _ _ _ hbig] at hc
    have hH1 : H (r1.headD 0) := by
      have : ¬ (4294967296 : Nat) ≤ (r1.headD 0).toNat := hbig; show _ < _; omega
    obtain ⟨a1, hrun1, hS1, hg1, hA1⟩ := bvar_step h.sum hS hA h1
    rcases h2 : snbW p N m1 k (i + 1) with _ | ⟨r2, m2⟩ <;> rw [h2] at hc
    · rw [snbW.k_stream_nested_bvars.none] at hc; cases hc
    rw [snbW.k_stream_nested_bvars.arm1] at hc
    obtain ⟨bs2, a2, hrun2, hS2, hg2, hA2, hd2, ht2⟩ := ih m1 m2 a1 (i + 1) r2 h2 hS1 hA1
    rcases h3 : callW p N "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
      rw [h3] at hc
    · rw [snbW.k_sl_cons.none] at hc; cases hc
    rw [snbW.k_sl_cons.arm1] at hc
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
    obtain ⟨hS3, hg3, hA3, hd3, ht3⟩ := cons_step h.sum hS2 hA2 ht2 hH1 hd2 h3
    refine ⟨decI (r1.headD 0) :: bs2, a2, ?_, hS3, (hg1.trans hg2).trans hg3, hA3,
      by simpa using hd3, by simpa using ht3⟩
    have hr : k.toNat - i.toNat = (k.toNat - (i.toNat + 1)) + 1 := by omega
    rw [hr, List.range'_succ]
    rw [hu] at hrun1
    rw [hi1] at hrun2
    simp only [List.mapM_cons, StateT.run_bind, hrun1, except_ok_bind, hrun2]
    rfl

end lists

end L.Ind

end
