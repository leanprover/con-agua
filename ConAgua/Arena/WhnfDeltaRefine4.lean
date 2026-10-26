import ConAgua.Arena.WhnfDeltaRefine3
import ConAgua.Arena.CoreNatOp

/-!
# δ and `Nat` literals: proofs of `WhnfDelta.lean`'s specs, part 4 (`reduce_nat`'s dispatch, `whnf_step`)

Split from `WhnfDeltaRefine.lean`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `reduce_nat`: the dispatch -/

/-- The `.const c us` arm of `reduceNat`'s `match ← view f`. -/
def redConstT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us : LsIdx) (b : EIdx) :
    AM (Option EIdx) := do
  let el ← emptyLevels
  if us != el then pure none else redSuccT r fe depth c b

/-- The `.app g a` arm of `reduceNat`'s `match ← view f`. -/
def redAppT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g a b : EIdx) : AM (Option EIdx) := do
  if g.tag == ETag.const then
    match ← view g with
    | .const c us => do
      let el ← emptyLevels
      if us != el then pure none else redBinT r fe depth c a b
    | _ => pure none
  else pure none

/-- `reduceNat` past the application node. -/
def redHeadT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) : AM (Option EIdx) := do
  match ← view f with
  | .const c us => redConstT r fe depth c us b
  | .app g a => redAppT r fe depth g a b
  | _ => pure none

theorem reduceNat_head_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e f b : EIdx) (a : AState)
    (h : (e.tag == ETag.app) = true) (hv : a.store.view e = some (.app f b)) :
    (reduceNat r fe depth e).run a = (redHeadT r fe depth f b).run a := by
  simp only [reduceNat, h, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, redHeadT,
    redConstT, redSuccT, redAppT, redBinT, redOpT, redWfT]
  rfl

theorem redHead_other (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) (a : AState)
    (v : ENodeView) (hvf : a.store.view f = some v) (hc : ∀ c us, v ≠ .const c us)
    (hp : ∀ g x, v ≠ .app g x) : (redHeadT r fe depth f b).run a = .ok (none, a) := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]
  cases v with
  | const c us => exact absurd rfl (hc c us)
  | app g x => exact absurd rfl (hp g x)
  | _ => rfl

theorem redHead_const (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b : EIdx) (a : AState)
    (c : NIdx) (us : LsIdx) (hvf : a.store.view f = some (.const c us)) :
    (redHeadT r fe depth f b).run a = (redConstT r fe depth c us b).run a := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]

theorem redHead_app (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (f b g x : EIdx) (a : AState)
    (hvf : a.store.view f = some (.app g x)) :
    (redHeadT r fe depth f b).run a = (redAppT r fe depth g x b).run a := by
  simp only [redHeadT, StateT.run_bind, view_run _ _ _ hvf, except_ok_bind]

theorem redConst_ne (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us el : LsIdx) (b : EIdx)
    (a : AState) (hel : emptyLevels.run a = .ok (el, a)) (hne : (us != el) = true) :
    (redConstT r fe depth c us b).run a = .ok (none, a) := by
  simp only [redConstT, StateT.run_bind, hel, except_ok_bind, hne]; rfl

theorem redConst_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (us el : LsIdx) (b : EIdx)
    (a : AState) (hel : emptyLevels.run a = .ok (el, a)) (heq : (us != el) = false) :
    (redConstT r fe depth c us b).run a = (redSuccT r fe depth c b).run a := by
  simp only [redConstT, StateT.run_bind, hel, except_ok_bind, heq]; rfl

theorem redApp_notconst (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (hg : (g.tag == ETag.const) = false) : (redAppT r fe depth g x b).run a = .ok (none, a) := by
  simp only [redAppT, hg]; rfl

theorem redApp_ne (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (hg : (g.tag == ETag.const) = true)
    (hv : a.store.view g = some (.const c us)) (hel : emptyLevels.run a = .ok (el, a))
    (hne : (us != el) = true) : (redAppT r fe depth g x b).run a = .ok (none, a) := by
  simp only [redAppT, hg, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hel, hne]; rfl

theorem redApp_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (g x b : EIdx) (a : AState)
    (c : NIdx) (us el : LsIdx) (hg : (g.tag == ETag.const) = true)
    (hv : a.store.view g = some (.const c us)) (hel : emptyLevels.run a = .ok (el, a))
    (heq : (us != el) = false) :
    (redAppT r fe depth g x b).run a = (redBinT r fe depth c x b).run a := by
  simp only [redAppT, hg, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hel, heq]; rfl


theorem CoreRef.congr {α : Type} [Inhabited α] {T T' : AM α} {a₀ : AState} {dec : List Word → α}
    {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop} (h : T.run a₀ = T'.run a₀)
    (hr : CoreRef T a₀ dec dn m₀ vis fe M eb r m ok) : CoreRef T' a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨c1, c2, c3⟩ := AM.congr_run h
  obtain ⟨hok, hA, hres, hok'⟩ := hr
  exact ⟨c1 ▸ hok, c2 ▸ hA, c3 ▸ hres, hok'⟩

section refs21
variable (p : Prog)

theorem callW_reduceNatK (hp : WhnfDeltaProg' p) (N F : Nat) (hF : N ≤ F) (hn2 : N ≤ 2 ^ 62)
    (hk : KnotUpTo p N) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hf : HW f) (hb : HW b) (hg3 : f >>> 28 = 3) (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0))
    (nn : NIdx) (uu : LsIdx) (hvf : a₀.store.view (decE f) = some (.const nn uu)) (r : List Word)
    (m' : Mem) (h : callW p N "reduce_nat_k" [mode, vis, d, f, b] s₀.mem = some (r, m')) :
    CoreRef (redConstT (coreKnot (decMode mode) fe id F) fe d.toNat nn uu (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatK_spec p hp.toWhnfDeltaProg n s₀ mode vis d f b) h
  unfold reduceNatKW at hW
  by_cases hbd : tcnt s₀.mem CONST (tierW f) ≤ idxW f
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ :=
    view_const_words s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg3
  rw [hview] at hvf
  have hvf' := Option.some.inj hvf
  injection hvf' with hn' hu'
  subst hn' hu'
  subst hn hu
  cases h1 : callW p n "pin_word" [52] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨hm1, -, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  dsimp only at hW
  have hel : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hC.pins
  have hbne : ∀ v w : Word, HW v → HW w → ((decI v : LsIdx) != decI w) = !decide (v = w) := by
    intro v w hv hw; simp only [bne, decI_beq v w hv hw]
  by_cases hne : tfld s₀.mem CONST (tierW f) (idxW f) 1 ≠ r₁.headD 0
  · rw [if_pos hne] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redConst_ne (coreKnot (decMode mode) fe id F) fe d.toNat (decI (tfld s₀.mem CONST (tierW f) (idxW f) 0)) (decI (tfld s₀.mem CONST (tierW f) (idxW f) 1))
      (decI (pinW s₀.mem 52)) (decE b) a₀ hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]
        have : tfld s₀.mem CONST (tierW f) (idxW f) 1 ≠ pinW s₀.mem 52 := by
          rw [← hr₁]; exact hne
        simp [this])
    refine (CRef.pure hC _ hz ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hne] at hW
  have hne' : tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52 := by
    rw [← hr₁]; simpa using hne
  cases h2 : callW p n "reduce_nat_succ" [mode, vis, d, tfld s₀.mem CONST (tierW f) (idxW f) 0,
      b] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hsucc := callW_reduceNatSucc p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM
    eb mode d _ b hS hnl hb r₂ m₂ h2
  have hcongr := redConst_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decI (tfld s₀.mem CONST (tierW f) (idxW f) 0)) (decI (tfld s₀.mem CONST (tierW f) (idxW f) 1))
      (decI (pinW s₀.mem 52)) (decE b) a₀ hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]; simp [hne'])
  have hsucc' := CoreRef.congr hcongr.symm hsucc
  obtain ⟨hok, hA, hres, hrw⟩ := hsucc'
  refine ⟨hok, hA, ?_, ?_⟩
  · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

end refs21


theorem natOpStored_run_pure (fe : IFEnv) (c : NIdx) (a : AState) :
    ∃ b, (natOpStored fe c).run a = .ok (b, a) := by
  unfold natOpStored
  cases fe.find? c with
  | none => exact ⟨false, rfl⟩
  | some ci => cases ci <;> exact ⟨_, rfl⟩

theorem bne_and_bne (x y : Word) : ((x != 0) && (y != 0)) = decide (x ≠ 0 ∧ y ≠ 0) := by
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx, hy]

section refs22
variable (p : Prog)

theorem callW_reduceNatAp (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (N F : Nat) (hF : N ≤ F)
    (hn2 : N ≤ 2 ^ 62) (hk : KnotUpTo p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hf : HW f) (hb : HW b)
    (hg4 : f >>> 28 = 4) (hsc : ¬(tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0))
    (g x : EIdx) (hvf : a₀.store.view (decE f) = some (.app g x)) (r : List Word) (m' : Mem)
    (h : callW p N "reduce_nat_ap" [mode, vis, d, f, b] s₀.mem = some (r, m')) :
    CoreRef (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat g x (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatAp_spec p hp.toWhnfDeltaProg n s₀ mode vis d f b) h
  unfold reduceNatApW at hW
  by_cases hbd : tcnt s₀.mem APP (tierW f) ≤ idxW f
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  obtain ⟨hviewf, hgw, hxw⟩ := view_app s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ hg4
  rw [hviewf] at hvf
  have hvf' := Option.some.inj hvf
  injection hvf' with hg' hx'
  subst hg' hx'
  generalize tfld s₀.mem APP (tierW f) (idxW f) 0 = gw at hW hgw hviewf
  generalize tfld s₀.mem APP (tierW f) (idxW f) 1 = xw at hW hxw hviewf
  by_cases g3 : gw >>> 28 ≠ 3
  · rw [if_pos g3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have ht : ((decE (gw)).tag == ETag.const) = false := by
      rw [decE_const_tag _ hgw]; exact beq_eq_false_iff_ne.mpr g3
    refine (CRef.pure hC _ (redApp_notconst _ fe d.toNat (decE gw) (decE xw) (decE b) a₀ ht) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g3] at hW
  have g3' : gw >>> 28 = 3 := by simpa using g3
  have ht : ((decE (gw)).tag == ETag.const) = true := by
    rw [decE_const_tag _ hgw]; exact beq_iff_eq.mpr g3'
  by_cases hs2 : tierW (gw) ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hs2] at hW; cases hW
  rw [if_neg hs2] at hW
  by_cases hb2 : tcnt s₀.mem CONST (tierW (gw)) ≤
      idxW (gw)
  · rw [if_pos hb2] at hW; cases hW
  rw [if_neg hb2] at hW
  obtain ⟨n_, us_, hview, hn, hu, hnl, hul⟩ := view_const_words s₀.mem a₀ hC.arena.1 _ hgw
    ⟨hs2, by simpa using hb2⟩ g3'
  subst hn hu
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 0 = cw at *
  generalize tfld s₀.mem CONST (tierW gw) (idxW gw) 1 = uw at *
  cases h1 : callW p n "pin_word" [52] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  obtain ⟨hm1, hflag, hr₁⟩ := callW_pinWord p hp.pinWord n s₀.mem 52 r₁ m₁ h1
  subst m₁
  simp only [show (52 : Word).toNat = 52 from rfl] at hr₁
  dsimp only at hW
  have hel : emptyLevels.run a₀ = .ok (decI (pinW s₀.mem 52), a₀) := pinEmptyLevels_run hC.pins
  have hbne : ∀ v w : Word, HW v → HW w → ((decI v : LsIdx) != decI w) = !decide (v = w) := by
    intro v w hv hw; simp only [bne, decI_beq v w hv hw]
  have hcond := fun (hh : uw = pinW s₀.mem 52) =>
    (by rw [hbne _ _ hul hC.pins.lv_lt.1]; simp [hh] : ((decI uw : LsIdx) != decI (pinW s₀.mem 52)) = false)
  by_cases hne : uw ≠ r₁.headD 0
  · rw [if_pos hne] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hz := redApp_ne (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
      (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel (by
        rw [hbne _ _ hul hC.pins.lv_lt.1]
        have : uw ≠ pinW s₀.mem 52 := by rw [← hr₁]; exact hne
        simp [this])
    refine (CRef.pure hC _ hz ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg hne] at hW
  have hne' : uw = pinW s₀.mem 52 := by rw [← hr₁]; simpa using hne
  have hcongrApp := redApp_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b) a₀
    (decI cw) (decI uw) (decI (pinW s₀.mem 52)) ht hview hel (hcond hne')
  -- `nat_bin_op_name`
  cases h2 : callW p n "nat_bin_op_name" [cw] s₀.mem with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  obtain ⟨t₂, ht₂, hm₂, -, hsel2, -⟩ := triple_of_callW
    (natBinOpNameL_spec p hp.natBinOpName n ⟨s₀.mem, Locals.init []⟩ hflag cw) h2
  have hm2 : m₂ = s₀.mem := by rw [← ht₂, hm₂]
  subst hm2
  dsimp only at hW
  cases h3 : callW p n "nat_op_stored" [vis, cw] s₀.mem with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, hS3, hres3, hfr3, hrh3⟩ := callW_natOpStored p hp n ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb cw
    hC hnl r₃ m₃ h3
  obtain ⟨b3, hb3⟩ := natOpStored_run_pure fe (decI cw) a₀
  have hst3 : AM.st (natOpStored fe (decI cw)) a₀ = a₀ := (AM.of_run_ok _ _ _ _ hb3).2.1
  have hbb3 : b3 = decBool r₃ := by
    have := (AM.of_run_ok _ _ _ _ hb3).2.2
    rw [hres3] at this; exact this.symm
  rw [hst3] at hS3
  have hbin : (natBinOpName (decI cw)).run a₀ = .ok (natBinOpSel (pinW s₀.mem ) cw, a₀) :=
    natBinOpName_run hC.pins cw hnl
  have hSP3 : SlotPre ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS3, hS.mode4, hS.eb_mode⟩
  have hbool : (natBinOpSel (pinW s₀.mem) cw && decBool r₃) = decide (r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0) := by
    rw [← hsel2]; exact bne_and_bne _ _
  have hredbin := redBin_run (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b) a₀
    (natBinOpSel (pinW s₀.mem) cw) (decBool r₃) hbin (by rw [hb3, hbb3])
  by_cases hgo : r₂.headD 0 ≠ 0 ∧ r₃.headD 0 ≠ 0
  · rw [if_pos hgo] at hW
    cases h4 : callW p n "reduce_nat_op" [mode, vis, d, cw, xw, b] m₃ with
    | none => rw [h4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [h4] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hop := callW_reduceNatOp p hp hno n F (by omega) (by omega) (hk.mono (by omega))
      ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b hSP3 hnl hxw hb r₄ m₄ h4
    have hcg : (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b)).run a₀ =
        (redOpT (coreKnot (decMode mode) fe id F) d.toNat (decI cw) (decE xw) (decE b)).run a₀ := by
      rw [hcongrApp, hredbin, hbool, decide_eq_true hgo]; rfl
    have hop' := CoreRef.congr hcg.symm hop
    obtain ⟨hok, hA, hres, hrw⟩ := hop'
    refine ⟨hok, CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr3) hA, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw
  · rw [if_neg hgo] at hW
    cases h4 : callW p n "reduce_nat_wf" [mode, vis, d, cw, xw, b] m₃ with
    | none => rw [h4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    rw [h4] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hwf := callW_reduceNatWf p hp n F (by omega) (by omega) (hk.mono (by omega))
      ⟨m₃, Locals.init []⟩ a₀ dn vis fe MM eb mode d cw xw b hSP3 hnl hxw hb r₄ m₄ h4
    have hcg : (redAppT (coreKnot (decMode mode) fe id F) fe d.toNat (decE gw) (decE xw) (decE b)).run a₀ =
        (redWfT (coreKnot (decMode mode) fe id F) fe d.toNat (decI cw) (decE xw) (decE b)).run a₀ := by
      rw [hcongrApp, hredbin, hbool, decide_eq_false hgo]; rfl
    have hwf' := CoreRef.congr hcg.symm hwf
    obtain ⟨hok, hA, hres, hrw⟩ := hwf'
    refine ⟨hok, CoreAfter.comp (KeptAll.refl _ _) (StackKept.of_const_frame hfr3) hA, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

end refs22


theorem view_nca (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (c : TRec) (hv : viewOK m h c)
    (hcg : (h >>> 28 = 0 ∧ c = BVAR) ∨ (h >>> 28 = 1 ∧ c = FVAR) ∨ (h >>> 28 = 2 ∧ c = SORT) ∨
      (h >>> 28 = 5 ∧ c = LAM) ∨ (h >>> 28 = 6 ∧ c = FORALL) ∨ (h >>> 28 = 7 ∧ c = LET) ∨
      (h >>> 28 = 8 ∧ c = LIT) ∨ (h >>> 28 = 9 ∧ c = PROJ)) :
    ∃ v, a.store.view (decE h) = some v ∧ (∀ c us, v ≠ .const c us) ∧ (∀ g x, v ≠ .app g x) := by
  rcases hcg with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact ⟨_, view_bvar m a hR h hh hv g, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨i, ty, hw⟩ := view_fvar m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨u, hw⟩ := view_sort m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_lam m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_forall m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_let m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩
  · obtain ⟨l, hw⟩ := view_lit m a hR h hh hv g
    exact ⟨_, hw, fun c us => nofun, fun c us => nofun⟩
  · exact ⟨_, (view_proj m a hR h hh hv g).1, fun c us => nofun, fun c us => nofun⟩

section refs23
variable (p : Prog)

theorem callW_reduceNatHead (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (N F : Nat) (hF : N ≤ F)
    (hn2 : N ≤ 2 ^ 62) (hk : KnotUpTo p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d f b : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (hf : HW f) (hb : HW b)
    (r : List Word) (m' : Mem)
    (h : callW p N "reduce_nat_head" [mode, vis, d, f, b] s₀.mem = some (r, m')) :
    CoreRef (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNatHead_spec p hp.toWhnfDeltaProg n s₀ mode vis d f b) h
  unfold reduceNatHeadW at hW
  by_cases hsc : tierW f ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  -- the tags that only check a bound
  have simple : ∀ (c : TRec), (f >>> 28 = 0 ∧ c = BVAR) ∨ (f >>> 28 = 1 ∧ c = FVAR) ∨ (f >>> 28 = 2 ∧ c = SORT) ∨
      (f >>> 28 = 5 ∧ c = LAM) ∨ (f >>> 28 = 6 ∧ c = FORALL) ∨ (f >>> 28 = 7 ∧ c = LET) ∨
      (f >>> 28 = 8 ∧ c = LIT) ∨ (f >>> 28 = 9 ∧ c = PROJ) →
      (if tcnt s₀.mem c (tierW f) ≤ idxW f then none else
        some ((0 : Word), (0 : Word), s₀.mem)) = some (r.headD 0, r.tail.headD 0, s'.mem) →
      CoreRef (redHeadT (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b)) a₀ decOptR dn
        s₀.mem vis fe MM eb r s'.mem ResW := by
    intro c hcg hW'
    by_cases hbd : tcnt s₀.mem c (tierW f) ≤ idxW f
    · rw [if_pos hbd] at hW'; cases hW'
    rw [if_neg hbd] at hW'
    simp only [Option.some.injEq, Prod.mk.injEq] at hW'
    obtain ⟨hr0, hr1, hm⟩ := hW'
    rw [← hm]
    obtain ⟨v, hv, hc, hp'⟩ := view_nca s₀.mem a₀ hC.arena.1 f hf c ⟨hsc, by simpa using hbd⟩ hcg
    refine (CRef.pure hC _ (redHead_other _ fe d.toNat _ (decE b) a₀ v hv hc hp') ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  by_cases g3 : f >>> 28 = 3
  · rw [if_pos g3] at hW
    cases h1 : callW p n "reduce_nat_k" [mode, vis, d, f, b] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    by_cases hbd : tcnt s₀.mem CONST (tierW f) ≤ idxW f
    · cases n with
      | zero => rw [callW_zero] at h1; cases h1
      | succ n' =>
      obtain ⟨s'', hs'', -, hW2⟩ := triple_of_callW (reduceNatK_spec p hp.toWhnfDeltaProg n' s₀ mode vis d f b) h1
      unfold reduceNatKW at hW2
      rw [if_pos hbd] at hW2; cases hW2
    obtain ⟨n_, us_, hview, -, -, -, -⟩ := view_const_words s₀.mem a₀ hC.arena.1 f hf
      ⟨hsc, by simpa using hbd⟩ g3
    have hK := callW_reduceNatK p hp n F (by omega) (by omega) (hk.mono (by omega)) s₀ a₀ dn vis fe MM eb
      mode d f b hS hf hb g3 hsc n_ us_ hview r₁ m₁ h1
    have hcg := redHead_const (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) a₀ n_ us_ hview
    have hK' := CoreRef.congr hcg.symm hK
    obtain ⟨hok, hA, hres, hrw⟩ := hK'
    refine ⟨hok, hA, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw
  rw [if_neg g3] at hW
  by_cases g4 : f >>> 28 = 4
  · rw [if_pos g4] at hW
    cases h1 : callW p n "reduce_nat_ap" [mode, vis, d, f, b] s₀.mem with
    | none => rw [h1] at hW; cases hW
    | some q₁ =>
    obtain ⟨r₁, m₁⟩ := q₁
    rw [h1] at hW
    dsimp only at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    by_cases hbd : tcnt s₀.mem APP (tierW f) ≤ idxW f
    · cases n with
      | zero => rw [callW_zero] at h1; cases h1
      | succ n' =>
      obtain ⟨s'', hs'', -, hW2⟩ := triple_of_callW (reduceNatAp_spec p hp.toWhnfDeltaProg n' s₀ mode vis d f b) h1
      unfold reduceNatApW at hW2
      rw [if_pos hbd] at hW2; cases hW2
    obtain ⟨hview, -, -⟩ := view_app s₀.mem a₀ hC.arena.1 f hf ⟨hsc, by simpa using hbd⟩ g4
    have hA := callW_reduceNatAp p hp hno n F (by omega) (by omega) (hk.mono (by omega))
      s₀ a₀ dn vis fe MM eb mode d f b hS hf hb g4 hsc _ _ hview r₁ m₁ h1
    have hcg := redHead_app (coreKnot (decMode mode) fe id F) fe d.toNat (decE f) (decE b) _ _ a₀ hview
    have hA' := CoreRef.congr hcg.symm hA
    obtain ⟨hok, hA2, hres, hrw⟩ := hA'
    refine ⟨hok, hA2, ?_, ?_⟩
    · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
    · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw
  rw [if_neg g4] at hW
  by_cases g0 : f >>> 28 = 0
  · rw [if_pos g0] at hW; exact simple BVAR (Or.inl ⟨g0, rfl⟩) hW
  rw [if_neg g0] at hW
  by_cases g1 : f >>> 28 = 1
  · rw [if_pos g1] at hW; exact simple FVAR (Or.inr (Or.inl ⟨g1, rfl⟩)) hW
  rw [if_neg g1] at hW
  by_cases g2 : f >>> 28 = 2
  · rw [if_pos g2] at hW; exact simple SORT (Or.inr (Or.inr (Or.inl ⟨g2, rfl⟩))) hW
  rw [if_neg g2] at hW
  by_cases g5 : f >>> 28 = 5
  · rw [if_pos g5] at hW; exact simple LAM (Or.inr (Or.inr (Or.inr (Or.inl ⟨g5, rfl⟩)))) hW
  rw [if_neg g5] at hW
  by_cases g6 : f >>> 28 = 6
  · rw [if_pos g6] at hW; exact simple FORALL (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g6, rfl⟩))))) hW
  rw [if_neg g6] at hW
  by_cases g7 : f >>> 28 = 7
  · rw [if_pos g7] at hW
    exact simple LET (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g7, rfl⟩)))))) hW
  rw [if_neg g7] at hW
  by_cases g8 : f >>> 28 = 8
  · rw [if_pos g8] at hW
    exact simple LIT (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨g8, rfl⟩))))))) hW
  rw [if_neg g8] at hW
  by_cases g9 : f >>> 28 ≠ 9
  · rw [if_pos g9] at hW; cases hW
  rw [if_neg g9] at hW
  have g9' : f >>> 28 = 9 := by simpa using g9
  exact simple PROJ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨g9', rfl⟩)))))))
    (by simpa using hW)

end refs23


/-- `ReduceNatSpec` with the L fuel bounded by the `2^62` that the knot's `whnf` slot needs. -/
def ReduceNatSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "reduce_nat" [mode, vis, d, e]
      (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decOptR s₀ a₀ dn vis fe MM eb
      ResW

section refs24
variable (p : Prog)

theorem callW_reduceNat (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (N F : Nat) (hF : N ≤ F)
    (hn2 : N ≤ 2 ^ 62) (hk : KnotUpTo p N) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d e : Word) (hS : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e)
    (r : List Word) (m' : Mem)
    (h : callW p N "reduce_nat" [mode, vis, d, e] s₀.mem = some (r, m')) :
    CoreRef (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) a₀ decOptR dn
      s₀.mem vis fe MM eb r m' ResW := by
  have hC := hS.rel
  cases N with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (reduceNat_spec p hp.toWhnfDeltaProg n s₀ mode vis d e) h
  unfold reduceNatW at hW
  have hap : ((decE e).tag == ETag.app) = (e >>> 28 == 4) := by
    by_cases g : e >>> 28 = 4
    · have := (decE_tag_app e he).mpr g
      rw [beq_iff_eq.mpr this, beq_iff_eq.mpr g]
    · have : ¬ (decE e).tag = ETag.app := fun h' => g ((decE_tag_app e he).mp h')
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr g]
  by_cases g4 : e >>> 28 ≠ 4
  · rw [if_pos g4] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    refine (CRef.pure hC _ (reduceNat_notapp _ fe d.toNat (decE e) a₀ (by rw [hap]; exact beq_eq_false_iff_ne.mpr g4)) ?_ ?_).core
    · simp only [decOptR, decOpt, ← hr0]; rfl
    · unfold ResW HW; rw [← hr0, ← hr1]; exact ⟨by decide, by decide⟩
  rw [if_neg g4] at hW
  have g4' : e >>> 28 = 4 := by simpa using g4
  by_cases hsc : tierW e ≠ 0 ∧ rdW (s₀.mem.arr64 CTL) 1 = 0
  · rw [if_pos hsc] at hW; cases hW
  rw [if_neg hsc] at hW
  by_cases hbd : tcnt s₀.mem APP (tierW e) ≤ idxW e
  · rw [if_pos hbd] at hW; cases hW
  rw [if_neg hbd] at hW
  obtain ⟨hview, hfw, hbw⟩ := view_app s₀.mem a₀ hC.arena.1 e he ⟨hsc, by simpa using hbd⟩ g4'
  generalize tfld s₀.mem APP (tierW e) (idxW e) 0 = fw at hW hview hfw
  generalize tfld s₀.mem APP (tierW e) (idxW e) 1 = bw at hW hview hbw
  cases h1 : callW p n "reduce_nat_head" [mode, vis, d, fw, bw] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hH := callW_reduceNatHead p hp hno n F (by omega) (by omega) (hk.mono (by omega))
    s₀ a₀ dn vis fe MM eb mode d fw bw hS hfw hbw r₁ m₁ h1
  have hcg := reduceNat_head_eq (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE fw) (decE bw) a₀
    (by rw [hap]; exact beq_iff_eq.mpr g4') hview
  have hH' := CoreRef.congr hcg.symm hH
  obtain ⟨hok, hA, hres, hrw⟩ := hH'
  refine ⟨hok, hA, ?_, ?_⟩
  · rw [hres]; simp only [decOptR, ← hr0, ← hr1]
  · unfold ResW at hrw ⊢; rw [← hr0, ← hr1]; exact hrw

/-- **`reduce_nat` refines `reduceNat`** (the statement of `reduceNat_refines`, with the fuel bound
`n ≤ 2 ^ 62` the knot's `whnf` slot needs, and the program/stub hypotheses explicit). -/
theorem reduceNat_refines' (hp : WhnfDeltaProg' p) (hno : NatOpResultOK p) (n : Nat) : ReduceNatSpec' p n := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk
  exact CoreSpec.of_call fun r m' h => callW_reduceNat p hp hno n F hF hn2 hk s₀ a₀ dn vis fe MM eb
    mode d e hS he r m' h

end refs24


/-! ## `whnf_step` -/

/-- The model of `whnf_step`: `(flag, result, memory)`. -/
def whnfStepW (p : Prog) (n : Nat) (m : Mem) (mode vis d e : Word) : Option (Word × Word × Mem) :=
  match callW p n "whnf_core" [mode, 0, vis, d, e] m with
  | none => none
  | some (r₁, m₁) =>
  match callW p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | none => none
  | some (r₂, m₂) =>
  if r₂.headD 0 ≠ 0 then some (1, r₂.tail.headD 0, m₂)
  else
  match callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | none => none
  | some (r₃, m₃) =>
  if r₃.headD 0 ≠ 0 then some (1, r₃.tail.headD 0, m₃) else some (0, r₁.headD 0, m₃)

theorem whnfStep_spec (p : Prog) (hp : WhnfDeltaProg p) (n : Nat) (s₀ : St) (mode vis d e : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_step" [mode, vis, d, e]
    ⦃fun r s' => LocEq s' s₀ ∧
      whnfStepW p n s₀.mem mode vis d e = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.whnfStep]
  simp only [callFn, whnfStepL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "whnf_core", callW_spec p n "reduce_nat", callW_spec p n "unfold_definition"] <;>
  simp_all [whnfStepW, Cmp.eval, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

theorem whnfStep_run_nat (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ e₂ : EIdx) (a a₁ a₂ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (some e₂, a₂)) :
    (whnfStep r fe depth e).run a = .ok (.cont e₂, a₂) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr]; rfl

theorem whnfStep_run_unf (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ e₂ : EIdx) (a a₁ a₂ a₃ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (none, a₂))
    (hu : (unfoldDefinition fe e₁).run a₂ = .ok (some e₂, a₃)) :
    (whnfStep r fe depth e).run a = .ok (.cont e₂, a₃) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr, hu]; rfl

theorem whnfStep_run_done (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e e₁ : EIdx) (a a₁ a₂ a₃ : AState)
    (hw : (r.whnfCore false depth e).run a = .ok (e₁, a₁))
    (hr : (reduceNat r fe depth e₁).run a₁ = .ok (none, a₂))
    (hu : (unfoldDefinition fe e₁).run a₂ = .ok (none, a₃)) :
    (whnfStep r fe depth e).run a = .ok (.done e₁, a₃) := by
  simp only [whnfStep, StateT.run_bind, hw, except_ok_bind, hr, hu]; rfl

/-- `WhnfStepSpec` with the fuel bound `n ≤ 2 ^ 62` (the knot's slots need it). -/
def WhnfStepSpec' (p : Prog) (n : Nat) : Prop :=
  ∀ (F : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d e : Word), n ≤ F → n ≤ 2 ^ 62 → SlotPre s₀ a₀ dn vis fe MM eb mode →
    HW e → KnotUpTo p n →
    CoreSpec p n "whnf_step" [mode, vis, d, e]
      (whnfStep (coreKnot (decMode mode) fe id F) fe d.toNat (decE e)) decStep s₀ a₀ dn vis fe MM eb
      ResW


section refs25
variable (p : Prog)

theorem whnfStep_refines' (hp : WhnfDeltaProg' p) (hlp : InstLPOK p) (n : Nat)
    (hrn : ∀ k, k ≤ n → ReduceNatSpec' p k) : WhnfStepSpec' p n := by
  intro F s₀ a₀ dn vis fe MM eb mode d e hF hn2 hS he hk
  have hC := hS.rel
  apply CoreSpec.of_call
  intro r m' h
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (whnfStep_spec p hp.toWhnfDeltaProg n s₀ mode vis d e) h
  unfold whnfStepW at hW
  have hkn : KnotOK p n := hk n (by omega)
  cases h1 : callW p n "whnf_core" [mode, 0, vis, d, e] s₀.mem with
  | none => rw [h1] at hW; cases hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  rw [h1] at hW
  dsimp only at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW
    (hkn.whnfCore F s₀ a₀ dn vis fe MM eb mode 0 d e (by omega) (by omega) hS he) h1
  rw [show ((0 : Word) != 0) = false from rfl] at hok1 hS₁ hres1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  generalize AM.st ((coreKnot (decMode mode) fe id F).whnfCore false d.toNat (decE e)) a₀ = a₁ at hrun1 hS₁
  have hSP1 : SlotPre ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₁, hS.mode4, hS.eb_mode⟩
  cases h2 : callW p n "reduce_nat" [mode, vis, d, r₁.headD 0] m₁ with
  | none => rw [h2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  rw [h2] at hW
  dsimp only at hW
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW
    (hrn n (by omega) F ⟨m₁, Locals.init []⟩ a₁ dn vis fe M₁ eb mode d (r₁.headD 0) (by omega) (by omega)
      hSP1 hrw1 (hk.mono (by omega))) h2
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  generalize AM.st (reduceNat (coreKnot (decMode mode) fe id F) fe d.toNat (decE (r₁.headD 0))) a₁ = a₂ at hrun2 hS₂
  by_cases hf2 : r₂.headD 0 ≠ 0
  · rw [if_pos hf2] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hsome : decOptR r₂ = some (decE (r₂.tail.headD 0)) := by simp only [decOptR, decOpt, if_neg hf2]
    rw [hsome] at hrun2
    have hz := whnfStep_run_nat (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) _ a₀ a₁ a₂
      (by rw [hrun1]; rfl) hrun2
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩
    · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
    · unfold ResW at hrw2 ⊢; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw2.2⟩
  rw [if_neg hf2] at hW
  have hnone : decOptR r₂ = none := by simp only [decOptR, decOpt]; rw [if_pos (by simpa using hf2)]
  rw [hnone] at hrun2
  have hSP2 : SlotPre ⟨m₂, Locals.init []⟩ a₂ dn vis fe M₂ eb mode := ⟨hS₂, hS.mode4, hS.eb_mode⟩
  cases h3 : callW p n "unfold_definition" [vis, r₁.headD 0] m₂ with
  | none => rw [h3] at hW; cases hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  rw [h3] at hW
  dsimp only at hW
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW
    (unfoldDefinition_refines' p hp n ⟨m₂, Locals.init []⟩ a₂ dn vis fe M₂ eb (r₁.headD 0) hS₂ hrw1 hlp) h3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  generalize AM.st (unfoldDefinition fe (decE (r₁.headD 0))) a₂ = a₃ at hrun3 hS₃
  by_cases hf3 : r₃.headD 0 ≠ 0
  · rw [if_pos hf3] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    rw [← hm]
    have hsome : decOptR r₃ = some (decE (r₃.tail.headD 0)) := by simp only [decOptR, decOpt, if_neg hf3]
    rw [hsome] at hrun3
    have hz := whnfStep_run_unf (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) _ a₀ a₁ a₂ a₃
      (by rw [hrun1]; rfl) hrun2 hrun3
    obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
    refine ⟨hok', ?_, ?_, ?_⟩
    · rw [hst']; exact ⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩
    · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp
    · unfold ResW at hrw3 ⊢; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw3.2⟩
  rw [if_neg hf3] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  rw [← hm]
  have hnone3 : decOptR r₃ = none := by simp only [decOptR, decOpt]; rw [if_pos (by simpa using hf3)]
  rw [hnone3] at hrun3
  have hz := whnfStep_run_done (coreKnot (decMode mode) fe id F) fe d.toNat (decE e) (decE (r₁.headD 0)) a₀ a₁ a₂ a₃
    (by rw [hrun1]; rfl) hrun2 hrun3
  obtain ⟨hok', hst', hres'⟩ := AM.of_run_ok _ _ _ _ hz
  refine ⟨hok', ?_, ?_, ?_⟩
  · rw [hst']; exact ⟨M₃, hS₃, (hK₁.trans hK₂).trans hK₃, (hSt₁.trans hSt₂).trans hSt₃⟩
  · rw [hres']; simp only [decStep, ← hr0, ← hr1]; simp [decH]
  · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hrw1⟩

end refs25

/-! ## The census-tagged statements: the stubs instantiated -/

section tagged
variable (p : Prog)

@[refines ConRon.Arena.reduceNat]
theorem reduceNat_refines (hp : WhnfDeltaProg' p) (n : Nat) : ReduceNatSpec' p n :=
  reduceNat_refines' p hp (natOpResultOK_of_agree hp.natAgree) n

end tagged

end L.Arena
