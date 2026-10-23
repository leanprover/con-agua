import ConAgua.Arena.IndInstallSpec19
import ConAgua.Arena.IndPos2SpecQ

/-!
# Refinements of `IndInstall`, part 20 (lane `indproofs2`, helper `install`): `checkAbsCtorSorts`,
`checkAbsCtorSortsAll`, the relation

Per constructor: the level parameters' check (`all_level_params_defined`'s stub), `NestCtx.hiAt`
(`nest_ctx_hi_at`, helper `pos`'s), the fields opened above the holes (`open_pis_at_fvars_f`'s
stub) and their sorts (`check_struct_field_sorts_i`, `installSimFsorts`).
-/


noncomputable section

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- One constructor's fields' universes, as the twin computes them after its level check. -/
def absOneAM (fe : IFEnv) (ctx : NestCtx) (b : Bool) (nF : Nat) (tyN : EIdx) : AM Unit := do
  let xq ← unwrapOr (← openPisAtFvarsF nF tyN (ctx.hiAt 0))
    (.internal "direct rec: abstracted constructor fields")
  let _ ← checkStructFieldSortsI V fe b false ctx.sort (ctx.hiAt 0) xq.1 [] nF
  pure ()

/-- A context word decoded below the tops. -/
theorem installCtxWord9 {m : Mem} {ctx : Word} {c : NestCtx}
    (hc : DecB (fun m => decCtx m ctx.toNat) m c) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    H (rdW (m.arr64 IW) (ctx + 9)) ∧ decI (rdW (m.arr64 IW) (ctx + 9)) = c.sort := by
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, -, -, -, -, h9, -⟩ := decCtx_some hcT
  obtain ⟨-, h9'⟩ := rec2IwH_trunc h9
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := ctx) (k := 9) h9' hsz
  rw [show (UInt64.ofNat 9 : Word) = 9 from rfl] at hv
  rw [hv]; exact ⟨hv32, hve⟩

/-- **`check_abs_ctor_sorts_one`'s model refines one constructor's fields' universes.** -/
theorem iaoW_sim {p : Prog} (hsum : SumProg p) (n : Nat) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} {ctx isP nF tyN hi : Word} {c : NestCtx} {b : Bool}
    (hS : StageR dn vis fe m a) (hc : DecB (fun m => decCtx m ctx.toNat) m c) (hty : H tyN)
    (hhi : hi.toNat = c.hiAt 0) (hb : (isP != 0) = b) :
    Sim (iaoW p n m vis ctx isP nF tyN hi) (absOneAM fe c b nF.toNat (decI tyN)) a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m') := by
  obtain ⟨hs32, hse⟩ := installCtxWord9 hc hS.2.2.2.1
  unfold iaoW absOneAM
  split
  · exact Sim.of_none
  rename_i hov
  refine Sim.bindK (K := iaoK1 p n vis isP nF hi (rdW (m.arr64 IW) (ctx + 9)))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none else iaoK2 (callW p n "check_struct_field_sorts_i"
      [vis, isP, 0, rdW (m.arr64 IW) (ctx + 9), hi, r1.tail.headD 0, r1.tail.tail.headD 0, 0, 0, nF] m1))
    (by simp [iaoK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iaoK1_none p n m₁ _ _ _ _ _ r h, if_pos h]
      · rw [iaoK1_some p n m₁ _ _ _ _ _ r h, if_neg h])
    (by
      have h := installSimKeep (p := p) (n := n) (openPisAtFvarsF_spec dn vis fe nF tyN hi hty) hS
      rw [hhi] at h; exact h) ?_
  rintro r1 x1 m1 a1 ⟨hS1, hg1, hd1⟩
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, if_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, if_false]
  show Sim _ (checkStructFieldSortsI V fe b false c.sort (c.hiAt 0) fvs [] nF.toNat >>= fun _ => pure ()) a1 _
  refine Sim.bindK (K := iaoK2) (body := fun _ m2 => some ([0], m2)) rfl (fun _ _ => rfl)
    (by
      have h := installSimFsorts (dn := dn) (fe := fe) hsum n isP 0
        (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF hs32 fvs [] ⟨hS1, hfd, hfb, by simp [decHL, hslice?], by simp⟩
        (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _)
      rw [hse, hhi, hb, show ((0 : Word) != 0) = false from rfl] at h
      exact h) ?_
  rintro r2 - m2 a2 ⟨hS2, hg2, -⟩
  exact Sim.ret ⟨hS2, hg1.trans hg2⟩

/-- A pointer slice decoded below the tops, below the top unless empty (an empty slice's offset is
whatever its record holds). -/
def PSlR0 {α : Type} (f : Mem → Nat → Option α) (xs : List α) (o l : Word) (m : Mem) : Prop :=
  DecB (fun m => decPL m (f m) o.toNat l.toNat) m xs ∧ (l = 0 ∨ o.toNat + l.toNat ≤ iwTop m)

theorem PSlR0.grow {α : Type} {f : Mem → Nat → Option α} (hf : ∀ q, OMono (fun m => f m q))
    {xs : List α} {o l : Word} {m m' : Mem} (h : PSlR0 f xs o l m) (hg : IWGrow m m') : PSlR0 f xs o l m' :=
  ⟨h.1.grow (OMono.decPL hf _ _) hg, h.2.imp id fun h2 => Nat.le_trans h2 hg.1⟩

theorem PSlR0.nil {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR0 f xs o l m) (hl : l = 0) : xs = [] := by
  have h1 := h.1; simp only [DecB, hl] at h1
  simpa [decPL] using h1.symm

theorem PSlR0.pslr {α : Type} {f : Mem → Nat → Option α} {xs : List α} {o l : Word} {m : Mem}
    (h : PSlR0 f xs o l m) (hl : l ≠ 0) : PSlR f xs o l m := ⟨h.1, h.2.resolve_left hl⟩

/-- The lookups of the fields' universes at the holes. -/
structure AbsProg (p : Prog) : Prop where
  hiAt : p.lookup "nest_ctx_hi_at" = some nestCtxHiAt
  one : p.lookup "check_abs_ctor_sorts_one" = some checkAbsCtorSortsOne
  abs : p.lookup "check_abs_ctor_sorts" = some checkAbsCtorSorts
  all : p.lookup "check_abs_ctor_sorts_all" = some checkAbsCtorSortsAll
  sum : SumProg p

/-- **`check_abs_ctor_sorts`' model refines `checkAbsCtorSorts`.** -/
theorem iacW_sim {p : Prog} (hP : AbsProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ctx isP : Word) (c : NestCtx) (b : Bool) (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (co cl oo ol : Word) (cs : List (IConstantVal × Nat))
      (os : List (List NestFieldKind × EIdx)),
    StageR dn vis fe m a → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCN cs co cl m → PSlR0 decKE os oo ol m →
    Sim (iacW p n m vis ctx isP co cl oo ol) (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a co cl oo ol cs os _ _ _ _; rw [iacW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a co cl oo ol cs os hS hc hcs hos
  by_cases hcl : cl = 0
  · rw [iacW_nil1 p n m vis ctx isP co cl oo ol hcl, hcs.nil hcl]
    exact Sim.ret ⟨hS, IWGrow.refl m⟩
  by_cases hol : ol = 0
  · rw [iacW_nil2 p n m vis ctx isP co cl oo ol hcl hol, hos.nil hol]
    have : ConRon.Arena.checkAbsCtorSorts V fe c b cs [] = pure () := by
      cases cs <;> simp [ConRon.Arena.checkAbsCtorSorts]
    rw [this]
    exact Sim.ret ⟨hS, IWGrow.refl m⟩
  obtain ⟨qc, ⟨cv, nF⟩, cs', rfl, hwc, hqcb, hdc, hcs'⟩ := partsPSl_cons (hcs.pslr hcl) hcl
  obtain ⟨qo, ⟨ks, e⟩, os', rfl, hwo, hqob, hdo, hos'⟩ := partsPSl_cons (hos.pslr hol) hol
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  -- the words read
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, hlps, hnP, -, -, -, -⟩ := decCtx_some hcT
  obtain ⟨lo, ll, hlo, hll, hlpsd⟩ := decAt_some hlps
  have hlolt := partsIwLt hll
  obtain ⟨hwlo, hlob, -⟩ := partsIwRd hlo (w := ctx + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hwll, hllb, -⟩ := partsIwRd hll (w := ctx + 3) (by rw [UInt64.toNat_add]; simp; omega)
  have hdoT : decKE (truncM m) qo = some (ks, e) := hdo
  simp only [decKE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hdoT
  obtain ⟨-, -, ee, hee, -, rfl⟩ := hdoT
  obtain ⟨heelt, hee'⟩ := rec2IwH_trunc hee
  obtain ⟨ew, hew, hew32, hewe⟩ := iwH_rdW_at (w := UInt64.ofNat qo) (k := 2) (by rw [hqo']; exact hee')
    hS.2.2.2.1
  rw [show (UInt64.ofNat 2 : Word) = 2 from rfl] at hew
  rw [iacW_cons p n m vis ctx isP co cl oo ol hcl hol, hwc, hwo, hwlo, hwll, hew]
  simp only [ConRon.Arena.checkAbsCtorSorts]
  have hlpsm : decHL m (UInt64.ofNat lo : Word).toNat (UInt64.ofNat ll : Word).toNat = some c.lps := by
    rw [UInt64.toNat_ofNat_of_lt' hlob, UInt64.toNat_ofNat_of_lt' hllb]
    exact DecB.get (f := fun m => (decHL m lo ll : Option (List NIdx))) (OMono.decHL _ _) hlpsd
  refine Sim.bindK (K := iacK1 p n vis ctx isP co cl oo ol (UInt64.ofNat qc) (UInt64.ofNat qo))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none
      else iacK2 p n vis ctx isP co cl oo ol (UInt64.ofNat qc) (UInt64.ofNat qo)
        (callW p n "nest_ctx_hi_at" [ctx, 0] m1)) (by simp [iacK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iacK1_none p n m₁ _ _ _ _ _ _ _ _ _ r h, if_pos h]
      · rw [iacK1_some p n m₁ _ _ _ _ _ _ _ _ _ r h, if_neg h])
    (by
      have h := installSimStub (p := p) (n := n) (allLevelParamsDefined_spec dn vis fe
        (UInt64.ofNat lo) (UInt64.ofNat ll) ew hew32 c.lps) ⟨hS, hlpsm⟩
      rw [hewe] at h; exact h) ?_
  rintro r1 ok m1 a1 ⟨hS1, hg1, hok1, -⟩
  by_cases h0 : r1.headD 0 = 0
  · simp only [h0, if_true]; exact Sim.of_none
  have hokt : ok = true := by rw [← hok1]; simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true]
  subst hokt
  simp only [h0, if_false]
  rw [if_pos trivial]
  -- `NestCtx.hiAt`
  have hc1 : decCtx m1 ctx.toNat = some c := hc.stab (decCtx_mono _) m1 hg1
  have hnPlt := partsIwLt hnP
  refine Sim.mstep (K := iacK2 p n vis ctx isP co cl oo ol (UInt64.ofNat qc) (UInt64.ofNat qo))
    (by simp [iacK2]) (fun r m₁ => iacK2_some p n m₁ vis ctx isP co cl oo ol _ _ r) fun r2 m2 h2 => ?_
  obtain ⟨s2, hs2, hpost2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (nestCtxHiAt_refines p hP.hiAt n _ ctx 0 c hc1 (by omega) (by omega)) h2
  obtain ⟨rfl, hr2⟩ := hpost2
  simp only at hs2; subst hs2
  rw [hr2]
  -- the constructor's fields
  have hdcT : decCN (truncM m) qc = some (cv, nF) := hdc
  obtain ⟨-, hnF⟩ := decCN_some hdcT
  have hnFlt := partsIwLt hnF
  obtain ⟨hwnF, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  have hwnF1 : rdW (m1.arr64 IW) (UInt64.ofNat qc + 1) = UInt64.ofNat nF := by
    rw [← hwnF]; simp only [rdW]; rw [show (UInt64.ofNat qc + 1 : Word).toNat = qc + 1 by
      rw [UInt64.toNat_add, hqc']; simp; omega, hg1.2.2.1 _ hnFlt]
  have hwe1 : rdW (m1.arr64 IW) (UInt64.ofNat qo + 2) = ew := by
    rw [← hew]; simp only [rdW]; rw [show (UInt64.ofNat qo + 2 : Word).toNat = qo + 2 by
      rw [UInt64.toNat_add, hqo']; simp; omega, hg1.2.2.1 _ heelt]
  rw [hwnF1, hwe1]
  refine Sim.congr (op := absOneAM fe c b nF ee >>= fun _ => ConRon.Arena.checkAbsCtorSorts V fe c b cs' os')
    ?_ (by simp only [absOneAM, bind_assoc, pure_bind])
  have hhiw : (UInt64.ofNat (c.hiAt 0) : Word).toNat = c.hiAt 0 := UInt64.toNat_ofNat_of_lt' hhi
  refine Sim.bindK (K := iacK3 p n vis ctx isP co cl oo ol) (body := fun _ m3 => iacK4
      (iacW p n m3 vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1))) (by simp [iacK3])
      (fun r m₁ => iacK3_some p n m₁ vis ctx isP co cl oo ol r)
    (Sim.callW_pos (Q := fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m1 m') (fun k r m' e => by
      obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
        (iao_spec p hP.one k _ vis ctx isP (UInt64.ofNat nF) ew (UInt64.ofNat (c.hiAt 0))) e
      have := iaoW_sim (p := p) hP.sum k hS1 (hc.grow (decCtx_mono _) hg1) hew32 hhiw hb r s'.mem hW
      rw [UInt64.toNat_ofNat_of_lt' hnFb, hewe] at this; dsimp only at this; exact this) n) ?_
  rintro - - m3 a3 ⟨hS3, hg3⟩
  have hg13 := hg1.trans hg3
  refine Sim.post (K := iacK4) rfl (fun _ _ => rfl)
    (ih m3 a3 (co + 1) (cl - 1) (oo + 1) (ol - 1) cs' os' hS3 (hc.grow (decCtx_mono _) hg13)
      (PSlR0.grow decCN_mono (⟨hcs'.1, Or.inr hcs'.2⟩ : PSlR0 decCN cs' (co + 1) (cl - 1) m) hg13)
      (PSlR0.grow decKE_mono (⟨hos'.1, Or.inr hos'.2⟩ : PSlR0 decKE os' (oo + 1) (ol - 1) m) hg13)) ?_
  rintro _ _ _ _ ⟨hS4, hg4⟩
  exact ⟨hS4, hg13.trans hg4⟩

/-- **`check_abs_ctor_sorts` refines `checkAbsCtorSorts`** (through `all_level_params_defined`'s,
`open_pis_at_fvars_f`'s stubs and `check_struct_field_sorts_i`'s pending contract): the context
decoded below the tops with its holes' bound below `2^64`, the constructors and their normal forms
slices decoded below the tops (an empty slice anywhere). -/
@[refines ConRon.Arena.checkAbsCtorSorts]
theorem checkAbsCtorSorts_refines (p : Prog) (hP : AbsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (ctx isP co cl oo ol : Word)
    (c : NestCtx) (b : Bool) (cs : List (IConstantVal × Nat)) (os : List (List NestFieldKind × EIdx))
    (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) (hS : StageR dn vis fe s₀.mem a₀)
    (hc : DecB (fun m => decCtx m ctx.toNat) s₀.mem c) (hcs : PSlR0 decCN cs co cl s₀.mem)
    (hos : PSlR0 decKE os oo ol s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts" [vis, ctx, isP, co, cl, oo, ol]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (iac_spec p hP.abs n s₀ vis ctx isP co cl oo ol) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (iacW_sim hP dn vis fe ctx isP c b hb hhi n _ a₀ co cl oo ol cs os hS hc hcs hos) hm
    ⟨hl, hok, hQ⟩

/-! ## `check_abs_ctor_sorts_all` -/

/-- A member's normal forms: a pointer to `[off, len]` of `[k.off, k.len, e]` pointers. -/
def decKES (m : Mem) (q : Nat) : Option (List (List NestFieldKind × EIdx)) :=
  decAt m (fun o l => decPL m (decKE m) o l) q

/-- **`check_abs_ctor_sorts_all`'s model refines `checkAbsCtorSortsAll`.** -/
theorem iaaW_sim {p : Prog} (hP : AbsProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (ctx isP : Word) (c : NestCtx) (b : Bool) (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (so sl oo ol : Word) (css : List (List (IConstantVal × Nat)))
      (oss : List (List (List NestFieldKind × EIdx))),
    StageR dn vis fe m a → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCNS css so sl m → PSlR0 decKES oss oo ol m →
    Sim (iaaW p n m vis ctx isP so sl oo ol) (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a
      (fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m m') := by
  induction n with
  | zero => intro m a so sl oo ol css oss _ _ _ _; rw [iaaW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a so sl oo ol css oss hS hc hcss hoss
  by_cases hsl : sl = 0
  · rw [iaaW_nil1 p n m vis ctx isP so sl oo ol hsl, hcss.nil hsl]
    exact Sim.ret ⟨hS, IWGrow.refl m⟩
  by_cases hol : ol = 0
  · rw [iaaW_nil2 p n m vis ctx isP so sl oo ol hsl hol, hoss.nil hol]
    have : ConRon.Arena.checkAbsCtorSortsAll V fe c b css [] = pure () := by
      cases css <;> simp [ConRon.Arena.checkAbsCtorSortsAll]
    rw [this]
    exact Sim.ret ⟨hS, IWGrow.refl m⟩
  obtain ⟨qc, cs, css', rfl, hwc, hqcb, hdc, hcss'⟩ := partsPSl_cons (hcss.pslr hsl) hsl
  obtain ⟨qo, os, oss', rfl, hwo, hqob, hdo, hoss'⟩ := partsPSl_cons (hoss.pslr hol) hol
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono (show decAt (truncM m)
    (decPL (truncM m) (decCN (truncM m))) qc = some cs from hdc)
  obtain ⟨oo2, ol2, hoo, hol2, hod, hob⟩ := partsAt decKE_mono (show decAt (truncM m)
    (decPL (truncM m) (decKE (truncM m))) qo = some os from hdo)
  have l1 := partsIwLt hcl; have l2 := partsIwLt hol2
  obtain ⟨w1, -, -⟩ := partsIwRd hco (w := UInt64.ofNat qc) hqc'
  obtain ⟨w2, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  obtain ⟨w3, -, -⟩ := partsIwRd hoo (w := UInt64.ofNat qo) hqo'
  obtain ⟨w4, -, -⟩ := partsIwRd hol2 (w := UInt64.ofNat qo + 1) (by rw [UInt64.toNat_add, hqo']; simp; omega)
  rw [UInt64.ofNat_toNat] at w1 w2 w3 w4
  rw [iaaW_cons p n m vis ctx isP so sl oo ol hsl hol, hwc, hwo, w1, w2, w3, w4]
  simp only [ConRon.Arena.checkAbsCtorSortsAll]
  refine Sim.bindK (K := iaaK1 p n vis ctx isP so sl oo ol) (body := fun _ m1 => iaaK2
      (iaaW p n m1 vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1))) (by simp [iaaK1])
      (fun r m₁ => iaaK1_some p n m₁ vis ctx isP so sl oo ol r)
    (fun r m' e => iacW_sim hP dn vis fe ctx isP c b hb hhi n m a co cl oo2 ol2 cs os hS hc ⟨hcd, hcb⟩
      ⟨hod, hob⟩ r m' (by
        obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (iac_spec p hP.abs n _ vis ctx isP co cl oo2 ol2) e
        exact hW)) ?_
  rintro - - m1 a1 ⟨hS1, hg1⟩
  refine Sim.post (K := iaaK2) rfl (fun _ _ => rfl)
    (ih m1 a1 (so + 1) (sl - 1) (oo + 1) (ol - 1) css' oss' hS1 (hc.grow (decCtx_mono _) hg1)
      (PSlR0.grow decCNS_mono (⟨hcss'.1, Or.inr hcss'.2⟩ : PSlR0 decCNS css' (so + 1) (sl - 1) m) hg1)
      (PSlR0.grow (fun q => OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q) (⟨hoss'.1, Or.inr hoss'.2⟩ : PSlR0 decKES oss' (oo + 1) (ol - 1) m) hg1)) ?_
  rintro _ _ _ _ ⟨hS2, hg2⟩
  exact ⟨hS2, hg1.trans hg2⟩

/-- **`check_abs_ctor_sorts_all` refines `checkAbsCtorSortsAll`** (through `check_abs_ctor_sorts`'
stubs and pending contract): every member's constructors and normal forms as slices of
`[off, len]` pointers decoded below the tops. -/
@[refines ConRon.Arena.checkAbsCtorSortsAll]
theorem checkAbsCtorSortsAll_refines (p : Prog) (hP : AbsProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (ctx isP so sl oo ol : Word)
    (c : NestCtx) (b : Bool) (css : List (List (IConstantVal × Nat)))
    (oss : List (List (List NestFieldKind × EIdx))) (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64)
    (hS : StageR dn vis fe s₀.mem a₀) (hc : DecB (fun m => decCtx m ctx.toNat) s₀.mem c)
    (hcss : PSlR0 decCNS css so sl s₀.mem) (hoss : PSlR0 decKES oss oo ol s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts_all" [vis, ctx, isP, so, sl, oo, ol]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a₀) ∧
      IWGrow s₀.mem s'.mem; ⊤⦄ :=
  triple_post (iaa_spec p hP.all n s₀ vis ctx isP so sl oo ol) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (iaaW_sim hP dn vis fe ctx isP c b hb hhi n _ a₀ so sl oo ol css oss hS hc hcss hoss) hm
    ⟨hl, hok, hQ⟩

end L.Ind
