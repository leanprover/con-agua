module

public import ConAgua.Arena.IndT.StreamRecsTop
import ConAgua.Arena.IndPosSpec.RootHoles
import ConAgua.Arena.LiftRefine
import ConAgua.Arena.IndSim
import ConAgua.Arena.IndInstallSpec.DomsW
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

/-- **`lift_entry`'s step**: con-ron's `liftLooseBVarsFast` at the core walk fuel, the stage
relation, the growth and the memos after. -/
theorem lift_step (hL : LiftProg p) (he : p.lookup "lift_entry" = some liftEntry) {n : Nat}
    {m m' : Mem} {a : AState} {h k : Word} {r : List Word} (hS : StageR vis fe m a) (hA : AbsOK m)
    (hh : H h) (hc : callW p n "lift_entry" [h, k, 0, CWF] m = some (r, m')) :
    ∃ a', (liftLooseBVarsFast coreWalkFuel k.toNat 0 (decI h)).run a = .ok (decI (r.headD 0), a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
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
  refine ⟨_, ?_, hS', hg, AFr.of_frame hfr (by decide) (by decide) hA⟩
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
    by_cases hbig : 4294967296 ≤ r1.headD 0
    · rw [snpW.k_lift_entry.abort1 _ _ _ _ _ _ _ hbig] at hc; cases hc
    rw [snpW.k_lift_entry.arm1 _ _ _ _ _ _ _ hbig] at hc
    have hH1 : H (r1.headD 0) := by
      have : ¬ (4294967296 : Nat) ≤ (r1.headD 0).toNat := hbig; show _ < _; omega
    obtain ⟨a1, hrun1, hS1, hg1, hA1⟩ := lift_step h.lift h.le hS hA hw2 h1
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

/-- `stream_nested_pins` through its run. -/
theorem snp_call (h : SnoProg p) {k : Word} {N : Nat} {m m' : Mem} {a : AState} {po pl : Word}
    {pins : List EIdx} {r : List Word}
    (hc : callW p N "stream_nested_pins" [k, po, pl] m = some (r, m')) (hS : StageR vis fe m a)
    (hA : AbsOK m) (hd : decHL m po.toNat pl.toNat = some pins) (hb : po.toNat + pl.toNat ≤ iwTop m) :
    ∃ ps a', (pins.mapM (liftLooseBVarsFast coreWalkFuel k.toNat 0)).run a = .ok (ps, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some ps ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  rcases N with _ | N
  · rw [callW_zero] at hc; cases hc
  exact snpW_ok h k (N + 1) m m' a po pl pins r
    (callW_model (M := fun mm => snpW p (N + 1) mm k po pl) (fun s => snpW_spec p h (N + 1) s k po pl) hc)
    hS hA hd hb

/-- `stream_nested_bvars` through its run, from `0`. -/
theorem snb_call (h : SnoProg p) {k : Word} {N : Nat} {m m' : Mem} {a : AState} {r : List Word}
    (hc : callW p N "stream_nested_bvars" [k, 0] m = some (r, m')) (hS : StageR vis fe m a)
    (hA : AbsOK m) :
    ∃ bs a', ((List.range k.toNat).mapM (fun j => internBVarE (k.toNat - 1 - j))).run a = .ok (bs, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
      decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some bs ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' := by
  rcases N with _ | N
  · rw [callW_zero] at hc; cases hc
  have := snbW_ok h k (N + 1) m m' a 0 r
    (callW_model (M := fun mm => snbW p (N + 1) mm k 0) (fun s => snbW_spec p h (N + 1) s k 0) hc) hS hA
  simpa [List.range_eq_range'] using this

end lists

/-! ## `stream_nested_dom` -/

section dom
variable {p : Prog} {vis : Word} {fe : IFEnv}

/-- **`stream_nested_dom` refines con-ron's `streamNestedDom`**: `0` exactly when it is `false`,
the stage relation, the growth and the memos after. -/
theorem snd_ok (h : SnoProg p) (k : Word) {N : Nat} {m m' : Mem} {a : AState}
    {dom lo ll po pl : Word} {lvls : List LIdx} {pins : List EIdx} {r : List Word}
    (hc : callW p N "stream_nested_dom" [dom, k, lo, ll, po, pl] m = some (r, m'))
    (hS : StageR vis fe m a) (hA : AbsOK m) (hdom : H dom)
    (hl : decHL m lo.toNat ll.toNat = some lvls) (hlb : lo.toNat + ll.toNat ≤ iwTop m)
    (hp : decHL m po.toNat pl.toNat = some pins) (hpb : po.toNat + pl.toNat ≤ iwTop m) :
    ∃ b a', (streamNestedDom (decI dom) k.toNat lvls pins).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ (r.headD 0 = 0 ↔ b = false) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (sndW_spec p h N _ dom k lo ll po pl) hc
  generalize s'.mem = m' at hm
  generalize r.headD 0 = v at hm ⊢
  rcases N with _ | N
  · simp [sndW] at hm
  rw [sndW.arm1] at hm
  -- `get_app_fn_f`
  rcases h1 : callW p N "get_app_fn_f" [CWF, dom] m with _ | ⟨r1, m1⟩ <;> rw [h1] at hm
  · rw [sndW.k_get_app_fn_f.none] at hm; cases hm
  obtain ⟨s1, rfl, -, hm1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (gafF_spec p h.sum.ad N _ [CWF, dom]) h1
  obtain ⟨x1, a1, hr1, hS1, hg1, hx1, hxd⟩ := (sumSim_of_relW (gafF_ok vis fe CWF dom hdom) hS) r1 _ hm1
  have hA1 : AbsOK s1.mem := AFr.of_frame (gafF_frame hm1) (by decide) (by decide) hA
  rw [CWF_eq] at hr1
  subst hxd
  generalize s1.mem = m1 at *
  have hR1 : ArenaR m1 a1 := hS1.check.arena.base
  by_cases hg3 : tagW (r1.headD 0) ≠ 3
  · rw [sndW.k_get_app_fn_f.arm1 _ _ _ _ _ _ _ _ _ _ hg3] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    have ht : ((decI (r1.headD 0) : EIdx).tag == ETag.const) = false :=
      beq_eq_false_iff_ne.mpr fun h' => hg3 ((decE_tag_const _ hx1).mp h')
    refine ⟨false, a1, ?_, hS1, hg1, hA1, by simp⟩
    simp only [ConRon.Arena.streamNestedDom, StateT.run_bind, hr1, except_ok_bind, ht]
    rfl
  have hg3 : tagW (r1.headD 0) = 3 := Classical.byContradiction hg3
  rw [sndW.k_get_app_fn_f.arm2 _ _ _ _ _ _ _ _ _ _ hg3] at hm
  -- the head's `e_view`
  rcases h2 : callW p N "e_view" [r1.headD 0] m1 with _ | ⟨r2, m2⟩ <;> rw [h2] at hm
  · rw [sndW.k_e_view.none] at hm; cases hm
  obtain ⟨s2, hs2, rfl, hne, hr2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (eView_spec p h.ev N _ (r1.headD 0)) h2
  rw [← hs2] at hm
  obtain ⟨hvok, hew⟩ := eViewW_const m1 _ hg3 (hr2 ▸ hne)
  obtain ⟨-, -, hus⟩ := L.Ind.view_const_f m1 a1 hR1 _ hx1 hvok hg3
  have hvc : a1.store.viewConst (decI (r1.headD 0)) = _ := viewConst_ok m1 a1 hR1 _ hx1 hvok
  rw [sndW.k_e_view.arm1] at hm
  have e2 : r2.tail.tail.headD 0 = tfld m1 CONST (tierW (r1.headD 0)) (idxW (r1.headD 0)) 1 := by
    rw [hr2, hew]; rfl
  rw [e2] at hm
  generalize tfld m1 CONST (tierW (r1.headD 0)) (idxW (r1.headD 0)) 1 = us at hm hus hvc
  -- `view_ls`
  rcases h3 : callW p N "view_ls" [us] m1 with _ | ⟨r3, m3⟩ <;> rw [h3] at hm
  · rw [sndW.k_view_ls.none] at hm; cases hm
  obtain ⟨s3, rfl, -, hm3⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (viewLs_specW p h.ln h.sum.ha h.pc h.vl N _ us) h3
  obtain ⟨ids, hr3, hS3, hg3', hd3, -⟩ := viewLsW_ok hm3 hS1 hus (rcPoolSmall hS1)
  have hA3 := hA1.iw (viewLsW_iwFrame hm3)
  simp only [decRL, getD_zero, Nat.zero_add, getD_one] at hd3
  obtain ⟨hd3, hb3⟩ := hd3
  generalize s3.mem = m3 at *
  rw [sndW.k_view_ls.arm1] at hm
  have hg13 := hg1.trans hg3'
  -- the levels against the firing data's
  rcases h4 : callW p N "sl_eq" [r3.headD 0, r3.tail.headD 0, lo, ll] m3 with _ | ⟨r4, m4⟩ <;>
    rw [h4] at hm
  · rw [sndW.k_sl_eq.none] at hm; cases hm
  obtain ⟨hm43, he4⟩ := slEq_stepK h.sum hS3 hd3 hb3 (by rw [decHL_grow hg13 hlb]; exact hl)
    (Nat.le_trans hlb hg13.iw) h4
  subst m4
  by_cases hq : r4.headD 0 = 0
  · rw [sndW.k_sl_eq.arm1 _ _ _ _ _ _ _ _ hq] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    have hne' : (ids == lvls) = false := by simpa using he4.mp hq
    have ht : ((decI (r1.headD 0) : EIdx).tag == ETag.const) = true :=
      beq_iff_eq.mpr ((decE_tag_const _ hx1).mpr hg3)
    refine ⟨false, a1, ?_, hS3, hg13, hA3, by simp⟩
    simp only [ConRon.Arena.streamNestedDom, StateT.run_bind, hr1, except_ok_bind, ht, ↓reduceIte,
      viewConst_run', hvc, hr3, hne']
    rfl
  rw [sndW.k_sl_eq.arm2 _ _ _ _ _ _ _ _ hq] at hm
  have hids : ids = lvls := Classical.byContradiction fun c => hq (he4.mpr c)
  -- the major's arguments
  rcases h5 : callW p N "get_app_args_f" [CWF, dom] m3 with _ | ⟨r5, m5⟩ <;> rw [h5] at hm
  · rw [sndW.k_get_app_args_f.none] at hm; cases hm
  obtain ⟨s5, rfl, -, hm5⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (gaaF_spec p h.sum.ad N _ [CWF, dom]) h5
  obtain ⟨args, a5, hr5, hS5, hg5, hxs5, hxb5⟩ :=
    (sumSim_of_relW (gaaF_ok (fun _ => none) vis fe CWF dom hdom) hS3) r5 _ hm5
  have hA5 := gaaF_afr hm5 hA3
  rw [getD_zero, getD_one] at hxs5 hxb5
  rw [CWF_eq] at hr5
  generalize s5.mem = m5 at *
  rw [sndW.k_get_app_args_f.arm1] at hm
  have hg15 := hg13.trans hg5
  -- the pins lifted
  rcases h6 : callW p N "stream_nested_pins" [k, po, pl] m5 with _ | ⟨r6, m6⟩ <;> rw [h6] at hm
  · rw [sndW.k_stream_nested_pins.none] at hm; cases hm
  obtain ⟨ps, a6, hr6, hS6, hg6, hA6, hd6, hb6⟩ := snp_call h h6 hS5 hA5
    (by rw [decHL_grow hg15 hpb]; exact hp) (Nat.le_trans hpb hg15.iw)
  rw [sndW.k_stream_nested_pins.arm1] at hm
  -- the index variables
  rcases h7 : callW p N "stream_nested_bvars" [k, 0] m6 with _ | ⟨r7, m7⟩ <;> rw [h7] at hm
  · rw [sndW.k_stream_nested_bvars.none] at hm; cases hm
  obtain ⟨bs, a7, hr7, hS7, hg7, hA7, hd7, hb7⟩ := snb_call h h7 hS6 hA6
  rw [sndW.k_stream_nested_bvars.arm1] at hm
  -- `sl_append`
  rcases h8 : callW p N "sl_append" [r6.headD 0, r6.tail.headD 0, r7.headD 0, r7.tail.headD 0] m7
    with _ | ⟨r8, m8⟩ <;> rw [h8] at hm
  · rw [sndW.k_sl_append.none] at hm; cases hm
  obtain ⟨hS8, hg8, hA8, hd8, hb8⟩ := append_step h.sum h.app hS7 hA7
    (Nat.le_trans hb6 hg7.iw) hb7 (by rw [decHL_grow hg7 hb6]; exact hd6) hd7 h8
  rw [sndW.k_sl_append.arm1] at hm
  have hg58 := (hg6.trans hg7).trans hg8
  -- the arguments against them
  rcases h9 : callW p N "sl_eq" [r5.headD 0, r5.tail.headD 0, r8.headD 0, r8.tail.headD 0] m8
    with _ | ⟨r9, m9⟩ <;> rw [h9] at hm
  · rw [sndW.k_sl_eq_2.none] at hm; cases hm
  obtain ⟨hm98, he9⟩ := slEq_stepK h.sum hS8 (by rw [decHL_grow hg58 hxb5]; exact hxs5)
    (Nat.le_trans hxb5 hg58.iw) hd8 hb8 h9
  subst m9
  rw [sndW.k_sl_eq_2.arm1] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  have ht : ((decI (r1.headD 0) : EIdx).tag == ETag.const) = true :=
    beq_iff_eq.mpr ((decE_tag_const _ hx1).mpr hg3)
  have hq' : (ids == lvls) = true := by simpa using hids
  refine ⟨args == ps ++ bs, a7, ?_, hS8, (hg15.trans hg58), hA8, ?_⟩
  · simp only [ConRon.Arena.streamNestedDom, StateT.run_bind, hr1, except_ok_bind, ht, ↓reduceIte,
      viewConst_run', hvc, hr3, hq', hr5, hr6, hr7]
    rfl
  · rw [he9]; simp

end dom

/-! ## `stream_nested_ok` -/

section ok
variable {p : Prog} {vis : Word} {fe : IFEnv}

theorem getD_succ0 (r : List Word) (i : Nat) : r.getD (i + 1) 0 = r.tail.getD i 0 := by
  cases r <;> simp

/-- **`stream_nested_ok` refines con-ron's `streamNestedOk`** under the stage relation: `0`
exactly when it is `false`, the growth and the memos after. -/
theorem sno_ok (h : SnoProg p) {N : Nat} {m m' : Mem} {a : AState} {ty mI rP : Word}
    {r : List Word} {f : IRecRuleFire} {r' : List Word}
    (hc : callW p N "stream_nested_ok" [ty, mI, rP, r.headD 0, r.tail.headD 0, r.tail.tail.headD 0,
        r.tail.tail.tail.headD 0, r.tail.tail.tail.tail.headD 0] m = some (r', m'))
    (hS : StageR vis fe m a) (hA : AbsOK m) (hty : H ty) (hf : decFireG m r f) :
    ∃ b a', (ConRon.Arena.streamNestedOk (decI ty) mI.toNat rP.toNat f).run a = .ok (b, a') ∧
      StageR vis fe m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ (r'.headD 0 = 0 ↔ b = false) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (snoW_spec p h N _ ty mI rP _ _ _ _ _) hc
  generalize s'.mem = m' at hm
  generalize r'.headD 0 = v at hm ⊢
  rcases N with _ | N
  · simp [snoW] at hm
  cases f with
  | plain =>
    have hf : r.headD 0 = 0 := hf
    rw [snoW.arm1 _ _ _ _ _ _ _ _ _ _ _ (by rw [hf]; decide)] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    exact ⟨true, a, rfl, hS, IWGrow.refl m, hA, by simp⟩
  | levels _ => exact absurd hf id
  | nested lvls pins =>
  obtain ⟨hk, ⟨hl, hlb⟩, ⟨hp, hpb⟩⟩ := hf
  simp only [getD_succ0, getD_zero] at hl hlb hp hpb
  rw [snoW.arm2 _ _ _ _ _ _ _ _ _ _ _ hk] at hm
  -- `strip_pis`
  rcases h1 : callW p N "strip_pis" [mI, ty] m with _ | ⟨r1, m1⟩ <;> rw [h1] at hm
  · rw [snoW.k_strip_pis.none] at hm; cases hm
  obtain ⟨s1, rfl, -, hm1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (stripPis_specF p h.sum.strip N _ mI ty) h1
  obtain ⟨o, a1, hr1, hS1, hg1, hdec⟩ := stripF_pis_ok vis fe mI ty hty m _ a r1 hm1 hS
  have hA1 := stripF_afr hm1 hA
  generalize s1.mem = m1 at *
  cases o with
  | none =>
    have h0 : r1.headD 0 = 0 := hdec
    rw [snoW.k_strip_pis.arm1 _ _ _ _ _ _ _ _ _ _ h0] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    refine ⟨false, a1, ?_, hS1, hg1, hA1, by simp⟩
    simp only [ConRon.Arena.streamNestedOk, StateT.run_bind, hr1, except_ok_bind]
    rfl
  | some q =>
  obtain ⟨pre, rest⟩ := q
  obtain ⟨h1', -, hbl, hbe⟩ := hdec
  rw [drop3_eq] at hbl hbe
  have h1ne : r1.headD 0 ≠ 0 := by rw [h1']; decide
  by_cases hg6 : tagW (r1.tail.tail.tail.headD 0) ≠ 6
  · rw [snoW.k_strip_pis.arm2 _ _ _ _ _ _ _ _ _ _ h1ne hg6] at hm
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
    have htag : (rest.tag == ETag.forallE) = false := by
      rw [← hbe]; exact beq_eq_false_iff_ne.mpr fun h' => hg6 ((decE_tag_forallE _ hbl).mp h')
    refine ⟨false, a1, ?_, hS1, hg1, hA1, by simp⟩
    simp only [ConRon.Arena.streamNestedOk, StateT.run_bind, hr1, except_ok_bind, htag]
    rfl
  have hg6' : tagW (r1.tail.tail.tail.headD 0) = 6 := Classical.byContradiction hg6
  rw [snoW.k_strip_pis.arm3 _ _ _ _ _ _ _ _ _ _ h1ne hg6'] at hm
  -- the major's binder
  rcases h2 : callW p N "e_view" [r1.tail.tail.tail.headD 0] m1 with _ | ⟨r2, m2⟩ <;> rw [h2] at hm
  · rw [snoW.k_e_view.none] at hm; cases hm
  obtain ⟨hm21, -, -, hdomH, -, hvb⟩ := eView_forall_callW h.ev hS1.check.arena.base hbl hg6' h2
  subst hm21
  -- the index count `mI - rP`, saturated like the twin's Nat subtraction
  obtain ⟨d, hd, hm⟩ : ∃ d : Word, d.toNat = mI.toNat - rP.toNat ∧
      snoW.j1 p N (r.tail.headD 0) (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0)
        (r.tail.tail.tail.tail.headD 0) (r2.tail.headD 0) d m2 = some (v, m') := by
    by_cases hlt : mI < rP
    · rw [snoW.k_e_view.arm1 _ _ _ _ _ _ _ _ _ _ hlt] at hm
      exact ⟨0, by have := UInt64.lt_iff_toNat_lt.mp hlt; simp; omega, hm⟩
    · rw [snoW.k_e_view.arm2 _ _ _ _ _ _ _ _ _ _ hlt] at hm
      exact ⟨_, UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp hlt), hm⟩
  rw [snoW.j1] at hm
  have hvb' : a1.store.viewBind rest =
      some (decI (r2.tail.headD 0), decI (r2.tail.tail.headD 0)) := by rw [← hbe]; exact hvb
  have htag : (rest.tag == ETag.forallE) = true := by
    rw [← hbe]; exact beq_iff_eq.mpr ((decE_tag_forallE _ hbl).mpr hg6')
  -- `stream_nested_dom`
  rcases h3 : callW p N "stream_nested_dom" [r2.tail.headD 0, d, r.tail.headD 0,
      r.tail.tail.headD 0, r.tail.tail.tail.headD 0, r.tail.tail.tail.tail.headD 0] m2
    with _ | ⟨r3, m3⟩ <;> rw [h3] at hm
  · rw [snoW.k_stream_nested_dom.none] at hm; cases hm
  rw [snoW.k_stream_nested_dom.arm1] at hm
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hm)
  obtain ⟨b, a3, hr3, hS3, hg3, hA3, hb3⟩ := snd_ok h d h3 hS1 hA1 hdomH
    (by rw [decHL_grow hg1 hlb]; exact hl) (Nat.le_trans hlb hg1.iw)
    (by rw [decHL_grow hg1 hpb]; exact hp) (Nat.le_trans hpb hg1.iw)
  refine ⟨b, a3, ?_, hS3, hg1.trans hg3, hA3, hb3⟩
  rw [hd] at hr3
  simp only [ConRon.Arena.streamNestedOk, StateT.run_bind, hr1, except_ok_bind, htag, ↓reduceIte,
    viewBind_run, hvb']
  exact hr3

/-- **`stream_nested_ok`'s step** (`SnoSim`, the obligation `sr1_ref` takes): the twin's step
from con-ron's `streamNestedOk_run`. -/
theorem snoSim_of {dn : NIdx → Option ConLeche.Name} (h : SnoProg p) : SnoSim p dn := by
  intro n vis fe env m a ty mI rP r f tyP fP hC hA _ hty htyP hf hfP r' m' hc
  obtain ⟨b, a', hrun, hS', hg, hA', hb⟩ := sno_ok h hc hC.stage hA hty hf
  obtain ⟨ps, -⟩ := ConRon.Bridge.Inductives.streamNestedOk_run hC.check.state htyP hfP hrun
  exact ⟨b, a', hrun, ⟨hC.of_pstep hS' hA' ps, hg, hA', ps.toCore hC.check⟩, hb⟩

end ok

end L.Ind

end
