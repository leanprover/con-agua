import ConAgua.Arena.DefEqMidLoops
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The batched ∀ descent: `defeq_peel` and `defeq_binders` (lane `defeq`)

The descent's loop is split for the proofs (`DefEq.lean`): `peel_leaf` (the twin's
`defeqPeelLeaf`), `peel_dom` (one level's domains), `peel_step` (the two binders' views, then the
domains), `peel_push` (the fresh free variable, pushed at the stack top), and the loop
`defeqPeelLoop` calling them. `fvs` is the stack slice `(fo, k)` with the top at `fo + k`; a
push grows it (`SpineR.push`), so the loop's post is `GrowRefP` (the stack below the old top kept,
the top grown); `defeq_binders` puts the top back.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of this file. -/
structure PeelProg (p : Prog) : Prop where
  leaf : p.lookup "peel_leaf" = some peelLeafL
  dom : p.lookup "peel_dom" = some peelDomL
  step : p.lookup "peel_step" = some peelStepL
  push : p.lookup "peel_push" = some peelPushL
  step2 : p.lookup "peel_step2" = some peelStep2L
  peel : p.lookup "defeq_peel" = some defeqPeelL
  binders : p.lookup "defeq_binders" = some defeqBindersL
  eview : p.lookup "e_view" = some L.Ind.eView
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar

/-! ## `intern_fvar` under `CoreS` -/

theorem fvinternW_hw (m : Mem) (a : AState) (hR : FVarR m a) (u ty w : Word) (m' : Mem)
    (hI : fvinternW m u ty = some (w, m')) : HW w := by
  exact consInternM_lt fvarCS_wf hR hI

theorem peel_keeps_cpl_internFVar (u : Nat) (ty : EIdx) : Keeps cpl (internE (.fvar u ty)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- **`intern_fvar` as a run under `CoreS`**: the twin's `internE (.fvar u ty)`, the relation at
the same maps, the stack and `CTL[136]` untouched, a handle word. -/
theorem peel_internFVar_core {p : Prog} (hp : PeelProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (u ty : Word) (hty : HW ty) (r : List Word)
    (hc : callW p n "intern_fvar" [u, ty] m = some (r, m')) :
    CoreRef (internE (.fvar u.toNat (decE ty))) a decH dn m vis fe M eb r m' ∧
      MemFrame [FVREC, tier1 FVREC, FVSLOT, tier1 FVSLOT, FVLP, tier1 FVLP] [26, 27] m m' := by
  obtain ⟨s', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec p hp.fvf hp.fvp hp.fvi n ⟨m, Locals.init []⟩ u ty) hc
  obtain ⟨hok, hD, hres⟩ := internFVar_D m a hS.arena u ty _ hty _ hI
  have hf := fvinternW_frame _ _ _ _ _ hI
  have hrun := AM.run_of_ok _ _ hok
  have hS' : CoreS dn s'.mem _ vis fe M eb :=
    hS.arena_frame hD (Keeps.run (peel_keeps_cpl_internFVar _ _) hrun) hf
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (by decide)
      (fun b hb => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
      (fun x hx => by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
        rcases hx with rfl | rfl <;> decide)
  have hspn : s'.mem.arr64 SPN = m.arr64 SPN := hf.arr SPN (by simp [tier1, FVREC, FVSLOT, FVLP, SPN]) (by decide)
  have h136 : rdW (s'.mem.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.ctl 136 (by simp)
  exact ⟨⟨hok, ⟨M, hS', KeptAll.refl _ _,
      StackKept.of_frame hf⟩,
    by rw [hres]; rfl, fvinternW_hw m a hS.arena.1.fvar u ty _ _ hI⟩, hf⟩

/-! ## Growing runs

`WhnfCoreProj.lean`'s `GrowRefP` with its lemmas, restated here (that file and `DefEqLeaves.lean`
both defined `lsNodeW_viewLen`, so they could not be imported together; DefEqLeaves' copy is now `defeq_lsNodeW_viewLen`). -/

theorem StackGrew.trans' {m₁ m₂ m₃ : Mem} (h₁ : StackGrew m₁ m₂) (h₂ : StackGrew m₂ m₃) :
    StackGrew m₁ m₃ :=
  h₁.trans h₂

theorem StackKept.toGrew' {m₁ m₂ : Mem} (h : StackKept m₁ m₂) : StackGrew m₁ m₂ :=
  h.toGrew

/-- `CoreRef` with the stack grown (`StackGrew`) instead of kept. -/
def GrowRefP {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m : Mem) (ok : List Word → Prop := ResH) : Prop :=
  AM.ok T a₀ ∧ (∃ M', CoreS dn m (AM.st T a₀) vis fe M' eb ∧ KeptAll M M' eb ∧ StackGrew m₀ m) ∧
    AM.res T a₀ = dec r ∧ ok r

/-- **A run, then a growing rest**. -/
theorem growRef_bind {α β : Type} [Inhabited α] [Inhabited β] {T₁ : AM α} {f : α → AM β}
    {a₀ : AState} {dec₁ : List Word → α} {dec : List Word → β} {dn : NIdx → Option ConLeche.Name}
    {m₀ m₁ m : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r₁ r : List Word}
    {ok₁ ok : List Word → Prop}
    (h₁ : GrowRefP T₁ a₀ dec₁ dn m₀ vis fe M eb r₁ m₁ ok₁)
    (h₂ : ∀ M', CoreS dn m₁ (AM.st T₁ a₀) vis fe M' eb → StackGrew m₀ m₁ →
      GrowRefP (f (dec₁ r₁)) (AM.st T₁ a₀) dec dn m₁ vis fe M' eb r m ok) :
    GrowRefP (T₁ >>= f) a₀ dec dn m₀ vis fe M eb r m ok := by
  obtain ⟨M', hS, hK, hSt⟩ := h₁.2.1
  obtain ⟨hok2, ⟨M'', hS'', hK'', hSt''⟩, hres2, hrw2⟩ := h₂ M' hS hSt
  have hT : (T₁ >>= f).run a₀ = (f (dec₁ r₁)).run (AM.st T₁ a₀) := by
    rw [StateT.run_bind, AM.run_of_ok _ _ h₁.1, h₁.2.2.1]; rfl
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans (AM.run_of_ok _ _ hok2))
  exact ⟨hok, hst ▸ ⟨M'', hS'', hK.trans hK'', hSt.trans' hSt''⟩, hres.trans hres2, hrw2⟩

/-! ## `peel_leaf` -/

/-- **`peel_leaf`'s model, both outcomes** (generated; `inst_list` lifted, the `defeq` slot through
its run). -/
l_model plE_spec (p : Prog) (hf : p.lookup "peel_leaf" = some peelLeafL)
  fns [hf ↦ plE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- The common hypotheses on the slice `fvs = (fo, k)` at the top of the stack. -/
structure FvsR (m : Mem) (fo k : Word) (fvs : Array EIdx) : Prop where
  spine : SpineR m fo k fvs
  top : spTop m = fo + k
  fit : fo.toNat + k.toNat < 2 ^ 63

theorem FvsR.le_top {m : Mem} {fo k : Word} {fvs : Array EIdx} (h : FvsR m fo k fvs) :
    fo.toNat + k.toNat ≤ (spTop m).toNat := by
  rw [h.top, UInt64.toNat_add]; have := h.fit; omega

theorem FvsR.kept {m m' : Mem} {fo k : Word} {fvs : Array EIdx} (h : FvsR m fo k fvs)
    (hk : StackKept m m') (hspn : (m.arr64 SPN).size < 2 ^ 63) : FvsR m' fo k fvs :=
  ⟨h.spine.keep hk.size hk.below h.le_top hspn, hk.1.trans h.top, h.fit⟩

theorem peel_word_add_toNat (d k : Word) (h : d.toNat + k.toNat < 2 ^ 64) : (d + k).toNat = d.toNat + k.toNat := by
  rw [UInt64.toNat_add]; omega

theorem toNat_zero_w : (0 : Word).toNat = 0 := rfl

/-- **`peel_leaf` refines `defeqPeelLeaf`, both outcomes**, from `inst_list`'s spec: the errors are
the `defeq` slot's. -/
theorem pl_ref (p : Prog) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (plE p (n + 1) s₀.mem mode vis d a b k fo)
      (defeqPeelLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs) a₀
      (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [plE]
  unfold defeqPeelLeaf
  rcases c1 : callW p n "inst_list" [a, fo, k, 0] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, plE.k_inst_list.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [plE.k_inst_list]
  have e₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb a fo k 0 fvs hs.rel ha hx.spine hx.le_top) c1
  rw [toNat_zero_w] at e₁
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ hst₁ => ?_)
  have hx₁ := hx.kept hst₁ hs.rel.spn
  rcases c2 : callW p n "inst_list" [b, fo, k, 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, plE.k_inst_list_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [plE.k_inst_list_2]
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hil n _ _ dn vis fe M₁ eb b fo k 0 fvs hS₁ hb hx₁.spine hx₁.le_top) c2
  rw [toNat_zero_w] at e₂
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  rcases c3 : callE p n "defeq" [mode, vis, d + k, r₁.headD 0, r₂.headD 0] m₂ with e | ⟨r₃, m₃⟩
  · intro hkE
    have := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
        ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) c3
    rwa [peel_word_add_toNat d k hdk] at this
  have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) (callW_of_callE c3)
  rw [peel_word_add_toNat d k hdk] at e₃
  obtain ⟨hrun, hP⟩ := e₃.post
  exact RefE.ret hrun ⟨hP.after, hP.res, hP.valid⟩

/-- **`peel_leaf` refines `defeqPeelLeaf`** at the knot, from `inst_list`'s spec (`pl_ref`'s ok
half). -/
@[refines ConRon.Arena.defeqPeelLeaf]
theorem peelLeaf_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_leaf" [mode, vis, d, a, b, k, fo]
      (defeqPeelLeaf (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs)
      decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (plE_spec p hp.leaf (n + 1) s₀ mode vis d a b k fo)
    (pl_ref p hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha hb fvs hx hdk)

/-! ## `peel_dom` -/

/-- One peeled level's domains, as the twin computes them inside `defeqPeel`. -/
def peelDomT (r : CoreFnsA) (d : Nat) (da db : EIdx) (k : Nat) (fvs : Array EIdx) :
    AM (Bool × EIdx) := do
  let t1 ← instantiateListFast coreWalkFuel da fvs 0
  let t2 ← if da == db then pure t1 else instantiateListFast coreWalkFuel db fvs 0
  let dq ← if da == db then pure true else r.defeq (d + k) t1 t2
  pure (dq, t2)

/-- `(dq, t2)`. -/
def decDom (r : List Word) : Bool × EIdx := (r.headD 0 != 0, decE (r.tail.headD 0))

/-- **`peel_dom`'s model, both outcomes** (generated; `inst_list` lifted, the `defeq` slot through
its run). -/
l_model pdE_spec (p : Prog) (hf : p.lookup "peel_dom" = some peelDomL)
  fns [hf ↦ pdE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`peel_dom` refines `peelDomT` (one level's domains), both outcomes**: the errors are the
`defeq` slot's. -/
theorem pd_ref (p : Prog) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da db k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW da) (hb : HW db)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (pdE p (n + 1) s₀.mem mode vis d da db k fo)
      (peelDomT (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE db) k.toNat fvs) a₀
      (CorePost decDom dn s₀.mem vis fe M eb ResW) := by
  simp only [pdE]
  unfold peelDomT
  rcases c1 : callW p n "inst_list" [da, fo, k, 0] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, pdE.k_inst_list.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [pdE.k_inst_list]
  have e₁ := CoreSpec.of_callW (hil n s₀ a₀ dn vis fe M eb da fo k 0 fvs hs.rel ha hx.spine hx.le_top) c1
  rw [toNat_zero_w] at e₁
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ hst₁ => ?_)
  by_cases he : da = db
  · have hbq : (decE da == decE db) = true := by rw [he]; exact beq_self_eq_true _
    rw [ite_eq_left he]
    simp only [hbq, ↓reduceIte, pure_bind]
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decDom, decH]; rfl) ⟨hw1, e₁.2.2.2⟩)
  rw [ite_eq_right he]
  have hbq : (decE da == decE db) = false := by
    rw [decE_beq_eq _ _ ha hb]; simp [he]
  simp only [hbq, Bool.false_eq_true, ↓reduceIte]
  have hx₁ := hx.kept hst₁ hs.rel.spn
  rcases c2 : callW p n "inst_list" [db, fo, k, 0] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, pdE.k_inst_list_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [pdE.k_inst_list_2]
  have e₂ := CoreSpec.of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (hil n _ _ dn vis fe M₁ eb db fo k 0 fvs hS₁ hb hx₁.spine hx₁.le_top) c2
  rw [toNat_zero_w] at e₂
  refine RefE.bind_core (w := id) e₂ (fun M₂ hS₂ _ => ?_)
  rcases c3 : callE p n "defeq" [mode, vis, d + k, r₁.headD 0, r₂.headD 0] m₂ with e | ⟨r₃, m₃⟩
  · intro hkE
    have := CoreSpecE.of_callE (s₀ := ⟨m₂, Locals.init []⟩)
      ((hkE n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
        ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) c3
    rw [peel_word_add_toNat d k hdk] at this
    exact ErrClaim.bind_left this
  have e₃ := CoreSpec.of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k) _ _ hF hn
      ⟨hS₂, hs.mode4, hs.eb_mode⟩ e₁.2.2.2 e₂.2.2.2) (callW_of_callE c3)
  rw [peel_word_add_toNat d k hdk] at e₃
  refine RefE.bind_core (w := id) e₃ (fun M₃ hS₃ _ => ?_)
  exact RefE.ret rfl (CorePost.ret hS₃ (by simp only [decDom, decBool, decH]; rfl)
    ⟨e₃.2.2.2, e₂.2.2.2⟩)

/-! ## `e_view` runs -/

theorem eViewW_lam (m : Mem) (h : Word) (hg : h >>> 28 = 5) (hne : L.Ind.eViewW m h ≠ []) :
    viewOK m h LAM ∧ L.Ind.eViewW m h = [5, tfld m LAM (tierW h) (idxW h) 0,
      tfld m LAM (tierW h) (idxW h) 1, 0] := by
  unfold L.Ind.eViewW at hne ⊢
  have h1 : ¬ (4294967295 : Word) < h := fun c => by simp [c] at hne
  simp only [h1, ite_false] at hne ⊢
  by_cases hs : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hs] at hne
  simp only [hs, ite_false] at hne ⊢
  have n0 : ¬ h >>> 28 = 0 := by rw [hg]; decide
  have n1 : ¬ h >>> 28 = 1 := by rw [hg]; decide
  have n2 : ¬ h >>> 28 = 2 := by rw [hg]; decide
  have n3 : ¬ h >>> 28 = 3 := by rw [hg]; decide
  have n4 : ¬ h >>> 28 = 4 := by rw [hg]; decide
  simp only [hg, ite_true] at hne ⊢
  by_cases c : tcnt m LAM (tierW h) ≤ idxW h
  · simp [c] at hne
  simp only [c, ite_false]
  exact ⟨⟨hs, by simpa using c⟩, rfl⟩

/-- **A run of `e_view` at a `∀`**: the memory kept, the binder's two words, the twin's
`viewBind`. -/
theorem eView_forall_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : h >>> 28 = 6)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ r.tail.headD 0 = tfld m FORALL (tierW h) (idxW h) 0 ∧
      r.tail.tail.headD 0 = tfld m FORALL (tierW h) (idxW h) 1 ∧
      HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨hv, hw⟩ := L.Ind.eViewW_forall m h hg (hr ▸ hne)
  rw [hw] at hr
  subst hr
  obtain ⟨-, h1, h2⟩ := view_forall m a hR h hh hv hg
  exact ⟨hm.symm, rfl, rfl, h1, h2, viewBind_forall m a hR h hh hv hg⟩

/-- **A run of `e_view` at a `λ`**. -/
theorem eView_lam_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : h >>> 28 = 5)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨hv, hw⟩ := eViewW_lam m h hg (hr ▸ hne)
  rw [hw] at hr
  subst hr
  obtain ⟨-, h1, h2⟩ := view_lam m a hR h hh hv hg
  exact ⟨hm.symm, h1, h2, viewBind_lam m a hR h hh hv hg⟩

/-! ## `peel_step2`, `peel_step` -/

/-- The second binder and the domains, as the twin computes them inside `defeqPeel`. -/
def peelStep2T (r : CoreFnsA) (d : Nat) (da b : EIdx) (k : Nat) (fvs : Array EIdx) :
    AM (Bool × EIdx × EIdx) := do
  match ← viewBind b with
  | none => failDanglingE
  | some (db, bb) => do
    let x ← peelDomT r d da db k fvs
    pure (x.1, x.2, bb)

/-- One peeled level, as the twin computes it inside `defeqPeel`: the two binders, the domains. -/
def peelStepT (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    AM (Bool × EIdx × EIdx × EIdx) := do
  match ← viewBind a with
  | none => failDanglingE
  | some (da, ba) => do
    let y ← peelStep2T r d da b k fvs
    pure (y.1, y.2.1, ba, y.2.2)

/-- `(dq, t2, bb)`. -/
def decPS2 (r : List Word) : Bool × EIdx × EIdx :=
  (r.headD 0 != 0, decE (r.tail.headD 0), decE (r.tail.tail.headD 0))

/-- `(dq, t2, ba, bb)`. -/
def decPS (r : List Word) : Bool × EIdx × EIdx × EIdx :=
  (r.headD 0 != 0, decE (r.tail.headD 0), decE (r.tail.tail.headD 0),
    decE (r.tail.tail.tail.headD 0))

/-- Three result words below `2^32`. -/
def Res3' (r : List Word) : Prop := HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0)

/-- Four result words below `2^32`. -/
def Res4 (r : List Word) : Prop :=
  HW (r.headD 0) ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧ HW (r.tail.tail.tail.headD 0)

/-- **`peel_step2`'s model, both outcomes** (generated; `e_view` lifted, `peel_dom` by its unified
model). -/
l_model ps2E_spec (p : Prog) (hf : p.lookup "peel_step2" = some peelStep2L)
    (hd : p.lookup "peel_dom" = some peelDomL)
  fns [hf ↦ ps2E list]
  specs [callW_spec p n "e_view", pdE_spec p hd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`peel_step2` refines `peelStep2T`, both outcomes**, at a `∀` handle `b`: the errors are
`peel_dom`'s. -/
theorem ps2_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hda : HW da) (hb : HW b)
    (hg : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (ps2E p (n + 1) s₀.mem mode vis d da b k fo)
      (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs) a₀
      (CorePost decPS2 dn s₀.mem vis fe M eb Res3') := by
  simp only [ps2E]
  rcases c1 : callW p n "e_view" [b] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, ps2E.k_e_view.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [ps2E.k_e_view]
  obtain ⟨k', rfl⟩ := callW_succ c1
  obtain ⟨rfl, -, -, hw1, hw2, hvb⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.1 hb hg c1
  have hT : (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs).run a₀ =
      (peelDomT (coreKnot (decMode mode) fe id F) d.toNat (decE da) (decE (r₁.tail.headD 0)) k.toNat fvs
        >>= fun x => pure (x.1, x.2, decE (r₁.tail.tail.headD 0))).run a₀ := by
    simp only [peelStep2T, StateT.run_bind, viewBind_run', hvb, except_ok_bind]
  refine RefE.of_run_eq hT ?_
  have H := pd_ref p hil k' (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
    mode d da _ k fo hs hda hw1 fvs hx hdk
  simp only [ps2E.k_peel_dom]
  rcases h2 : pdE p (k' + 1) s₀.mem mode vis d da (r₁.tail.headD 0) k fo with e | ⟨r₂, m₂⟩
  · rw [h2] at H; exact fun hkE => ErrClaim.bind_left (H (hkE.mono (by omega)))
  rw [h2] at H
  obtain ⟨y, a', hrun, hP⟩ := H
  exact RefE.bind_right hrun (RefE.ret rfl ⟨hP.after, by rw [hP.res]; rfl,
    ⟨hP.valid.1, hP.valid.2, hw2⟩⟩)

/-- **`peel_step`'s model, both outcomes** (generated; `e_view` lifted, `peel_step2` by its unified
model). -/
l_model psE_spec (p : Prog) (hf : p.lookup "peel_step" = some peelStepL)
    (h2 : p.lookup "peel_step2" = some peelStep2L) (hd : p.lookup "peel_dom" = some peelDomL)
  fns [hf ↦ psE list]
  specs [callW_spec p n "e_view", ps2E_spec p h2 hd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`peel_step` refines `peelStepT`, both outcomes**, at two `∀` handles: the errors are
`peel_step2`'s. -/
theorem ps_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hga : a >>> 28 = 6) (hgb : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (psE p (n + 1) s₀.mem mode vis d a b k fo)
      (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs) a₀
      (CorePost decPS dn s₀.mem vis fe M eb Res4) := by
  simp only [psE]
  rcases c1 : callW p n "e_view" [a] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, psE.k_e_view.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [psE.k_e_view]
  obtain ⟨k', rfl⟩ := callW_succ c1
  obtain ⟨rfl, -, -, hw1, hw2, hva⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.1 ha hga c1
  have hT : (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs).run a₀ =
      (peelStep2T (coreKnot (decMode mode) fe id F) d.toNat (decE (r₁.tail.headD 0)) (decE b) k.toNat fvs
        >>= fun y => pure (y.1, y.2.1, decE (r₁.tail.tail.headD 0), y.2.2)).run a₀ := by
    simp only [peelStepT, StateT.run_bind, viewBind_run', hva, except_ok_bind]
  refine RefE.of_run_eq hT ?_
  have H := ps2_ref p hp hil k' (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
    mode d _ b k fo hs hw1 hb hgb fvs hx hdk
  simp only [psE.k_peel_step2]
  rcases h2 : ps2E p (k' + 1) s₀.mem mode vis d (r₁.tail.headD 0) b k fo with e | ⟨r₂, m₂⟩
  · rw [h2] at H; exact fun hkE => ErrClaim.bind_left (H (hkE.mono (by omega)))
  rw [h2] at H
  obtain ⟨y, a', hrun, hP⟩ := H
  exact RefE.bind_right hrun (RefE.ret rfl ⟨hP.after, by rw [hP.res]; rfl,
    ⟨hP.valid.1, hP.valid.2.1, hw2, hP.valid.2.2⟩⟩)

/-- **`peel_step` refines `peelStepT`** at two `∀` handles (`ps_ref`'s ok half). -/
theorem peelStep_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hga : a >>> 28 = 6) (hgb : b >>> 28 = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_step" [mode, vis, d, a, b, k, fo]
      (peelStepT (coreKnot (decMode mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs)
      decPS s₀ a₀ dn vis fe M eb Res4 :=
  RefE.coreSpec (psE_spec p hp.step hp.step2 hp.dom (n + 1) s₀ mode vis d a b k fo)
    (ps_ref p hp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha hb hga hgb fvs hx hdk)

/-! ## `peel_push` -/

/-- A slice survives a change that leaves the stack array alone. -/
theorem SpineR.of_spnP {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hs : m'.arr64 SPN = m.arr64 SPN) : SpineR m' off cnt xs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by rw [hs]; exact h2, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [spW, hs] at h3 ⊢; exact h3 i hi
  · simp only [spW, hs] at h4 ⊢; exact h4 i hi

/-- The model of `peel_push` past `intern_fvar`'s run: the word at `fo + k`, the top at
`fo + k + 1`. -/
def peelPushK (fo k : Word) (res : Option (List Word × Mem)) : Option (Word × Mem) :=
  match res with
  | none => none
  | some (r, m) =>
    if (fo + k).toNat < (m.arr64 SPN).size ∧ 136 < (m.arr64 CTL).size then
      some (r.headD 0, (m.set64 SPN (fo + k) (r.headD 0)).set64 CTL 136 (fo + k + 1))
    else none

theorem pushK_ok (fo k : Word) (r : List Word) (m : Mem) (h1 : (fo + k).toNat < (m.arr64 SPN).size)
    (h2 : 136 < (m.arr64 CTL).size) :
    peelPushK fo k (some (r, m)) = some (r.headD 0, (m.set64 SPN (fo + k) (r.headD 0)).set64 CTL 136 (fo + k + 1)) := by
  simp only [peelPushK, h1, h2, and_self, ↓reduceIte]

theorem peelPush_spec (p : Prog) (hp : PeelProg p) (n : Nat) (s₀ : St) (d k fo t2 : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "peel_push" [d, k, fo, t2]
    ⦃fun r s' => LocEq s' s₀ ∧ peelPushK fo k (callW p n "intern_fvar" [d + k, t2] s₀.mem) =
      some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.push]
  simp only [callFn, peelPushL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, callW_spec p n "intern_fvar"] <;>
    finish [pushK_ok]

/-- **A run of `peel_push`**: the twin's `internFVarE (d + k) t2`, the slice `fvs` grown by the
new free variable, the top at `fo + k + 1`. -/
theorem peelPush_run {p : Prog} (hp : PeelProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    (hS : CoreS dn m a vis fe M eb) (d k fo t2 : Word) (ht : HW t2) (fvs : Array EIdx)
    (hx : FvsR m fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) (r : List Word)
    (hc : callW p (n + 1) "peel_push" [d, k, fo, t2] m = some (r, m')) :
    GrowRefP (internFVarE (d.toNat + k.toNat) (decE t2)) a decH dn m vis fe M eb r m' ∧
      FvsR m' fo (k + 1) (fvs.push (decE (r.headD 0))) := by
  unfold internFVarE
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (peelPush_spec p hp n ⟨m, Locals.init []⟩ d k fo t2) hc
  cases hc1 : callW p n "intern_fvar" [d + k, t2] m with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  simp only [peelPushK] at hW
  split at hW
  · rename_i hb
    obtain ⟨hb1, hb2⟩ := hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨e₁, hf₁⟩ := peel_internFVar_core hp hS (d + k) t2 ht r₁ hc1
    rw [peel_word_add_toNat d k hdk] at e₁
    obtain ⟨hok, ⟨M₁, hS₁, hK₁, hst₁⟩, hres, hw⟩ := e₁
    have hfvs₁ := hx.kept hst₁ hS.spn
    have hfoK : (fo + k).toNat = fo.toNat + k.toNat := by
      rw [UInt64.toNat_add]; have := hx.fit; omega
    have hk1 : fo.toNat + k.toNat + 1 < 2 ^ 63 := by
      have e : (m₁.arr64 SPN).size = (m.arr64 SPN).size := hf₁.size SPN
      have := hS.spn; omega
    have hpush := hfvs₁.spine.push (hf₁.size SPN ▸ hS.spn) (by rw [← hfoK]; exact hb1) _ hw
    -- the two writes
    have hfr : MemFrame [SPN] [136] m₁ s'.mem := by
      rw [← hm]
      exact (MemFrame.set64 m₁ SPN (by decide) _ _).mono (by simp) (by simp) |>.trans
        ((MemFrame.setCtl _ 136 _).mono (by simp) (by simp))
    have hS₂ := hS₁.frame_stk hfr (by simp) (by simp)
    have hspn' : s'.mem.arr64 SPN = (m₁.set64 SPN (fo + k) (r₁.headD 0)).arr64 SPN := by
      rw [← hm]; exact Mem.arr64_set64_ne _ _ _ _ _ (by decide)
    have htop : spTop s'.mem = fo + k + 1 := by
      rw [← hm]; unfold spTop
      rw [rdW_set64L, ite_eq_left ⟨rfl, rfl, by rw [size_set64L]; exact hb2⟩]
    have hk1' : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; have := hx.fit; omega
    refine ⟨⟨hok, ⟨M₁, hS₂, hK₁, ?_⟩, by rw [hres, decH, hr]; rfl, by unfold ResH; rw [← hr]; exact hw⟩,
      ⟨by rw [← hr]; exact hpush.of_spnP hspn', by rw [htop, UInt64.add_assoc], by rw [hk1']; omega⟩⟩
    -- the stack grew
    have hsz : (s'.mem.arr64 SPN).size = (m.arr64 SPN).size := by
      rw [hspn', size_set64L]; exact hst₁.size
    refine ⟨?_, hsz, fun i hi => ?_, hst₁.bstk.trans (BKept.of_frame hfr (by decide) (by decide)),
      hst₁.pool.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩
    · rw [htop, hx.top, UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_add, UInt64.toNat_one]
      have := hx.fit; omega
    · have hi' : i ≠ fo + k := fun h => by rw [h, ← hx.top] at hi; exact absurd hi (by simp)
      unfold spW
      rw [hspn', rdW_set64L, ite_eq_right (fun h => hi' h.2.1.symm)]
      exact hst₁.below i hi
  · cases hW

/-! ## The twin's descent, one level at a time -/

theorem viewBind_bind_run {β : Type} (h : EIdx) (f : Option (EIdx × EIdx) → AM β) (s : AState) :
    (viewBind h >>= f).run s = (f (s.store.viewBind h)).run s := by
  simp only [StateT.run_bind, viewBind_run', except_ok_bind]

/-- One level of the twin's `defeqPeel`, verbatim, the recursive call abstracted as `cont` (the
equation compiler cannot produce `defeqPeel`'s unfolding lemma in its heartbeat budget; con-ron's
`Bridge/Core/Arms/DefeqPeel.lean` states the two unfoldings the same way, by `delta` and `rfl`). -/
def peelLvl (r : CoreFnsA) (d : Nat) (peel : Nat)
    (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) : AM Bool := do
  if a == b then pure true
  else if peel = 0 || a.tag != ETag.forallE || b.tag != ETag.forallE then
    defeqPeelLeaf r d a b k fvs
  else
    match ← viewBind a with
    | none => failDanglingE
    | some (da, ba) =>
      match ← viewBind b with
      | none => failDanglingE
      | some (db, bb) => do
        let sameDom := da == db
        let t1 ← instantiateListFast coreWalkFuel da fvs 0
        let t2 ← if sameDom then pure t1
                 else instantiateListFast coreWalkFuel db fvs 0
        let dq ← if sameDom then pure true else r.defeq (d + k) t1 t2
        if !dq then pure false
        else do
          let fv ← internFVarE (d + k) t2
          cont ba bb (k + 1) (fvs.push fv)

theorem defeqPeel_succ_eq (r : CoreFnsA) (d p : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d (p + 1) a b k fvs = peelLvl r d (p + 1) (defeqPeel r d p) a b k fvs := by
  delta defeqPeel peelLvl
  exact rfl

theorem defeqPeel_zero_eq (r : CoreFnsA) (d : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx) :
    defeqPeel r d 0 a b k fvs = peelLvl r d 0 (defeqPeelLeaf r d) a b k fvs := by
  delta defeqPeel peelLvl
  exact rfl

theorem peelLvl_eq_run (r : CoreFnsA) (d peel : Nat) (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (s : AState) (h : (a == b) = true) :
    (peelLvl r d peel cont a b k fvs).run s = .ok (true, s) := by
  simp only [peelLvl, h, ↓reduceIte]; rfl

theorem peelLvl_leaf_run (r : CoreFnsA) (d peel : Nat) (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (s : AState) (h : (a == b) = false)
    (hl : (decide (peel = 0) || a.tag != ETag.forallE || b.tag != ETag.forallE) = true) :
    (peelLvl r d peel cont a b k fvs).run s = (defeqPeelLeaf r d a b k fvs).run s := by
  simp only [peelLvl, h, hl, Bool.false_eq_true, ↓reduceIte]

theorem peelLvl_step_run (r : CoreFnsA) (d peel : Nat) (cont : EIdx → EIdx → Nat → Array EIdx → AM Bool)
    (a b : EIdx) (k : Nat) (fvs : Array EIdx) (s : AState) (h : (a == b) = false)
    (hl : (decide (peel = 0) || a.tag != ETag.forallE || b.tag != ETag.forallE) = false) :
    (peelLvl r d peel cont a b k fvs).run s = (peelStepT r d a b k fvs >>= fun x =>
      if !x.1 then pure false else do
        let fv ← internFVarE (d + k) x.2.1
        cont x.2.2.1 x.2.2.2 (k + 1) (fvs.push fv)).run s := by
  simp only [peelLvl, h, hl, Bool.false_eq_true, ↓reduceIte, peelStepT, bind_assoc]
  rw [viewBind_bind_run, viewBind_bind_run]
  cases s.store.viewBind a with
  | none => rfl
  | some x =>
  obtain ⟨da, ba⟩ := x
  simp only [peelStep2T, bind_assoc, pure_bind]
  rw [viewBind_bind_run, viewBind_bind_run]
  cases s.store.viewBind b with
  | none => rfl
  | some y =>
  obtain ⟨db, bb⟩ := y
  simp only [peelDomT, bind_assoc, pure_bind]
  cases hdd : (da == db) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc, pure_bind, Bool.not_true]

/-! ## `defeq_peel`: the loop -/

/-- **`defeq_peel`'s model, both outcomes** (the loop `peelE.loop1`: `peel_leaf`, `peel_step`,
`peel_push` through their runs, `callE`). -/
l_model defeqPeel_specE (p : Prog) (hf : p.lookup "defeq_peel" = some defeqPeelL)
  fns [hf ↦ peelE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified

/-- **What the descent's errors claim from**: the knot's slots up to fuel `n` (through `peel_leaf`'s
and `peel_step`'s refinements) and the verdict closure (`peel_push`, the lifted callees). -/
structure PeelG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true

theorem PeelG.mono {p : Prog} {n n' : Nat} (h : PeelG p n) (hn : n' ≤ n) : PeelG p n' :=
  ⟨h.knot.mono hn, h.nv⟩

/-! ## The loop refines `defeqPeel` -/

theorem defeqPeel_eq_run (r : CoreFnsA) (d peel : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx)
    (s : AState) (h : (a == b) = true) : (defeqPeel r d peel a b k fvs).run s = .ok (true, s) := by
  cases peel with
  | zero => rw [defeqPeel_zero_eq]; exact peelLvl_eq_run _ _ _ _ _ _ _ _ _ h
  | succ p => rw [defeqPeel_succ_eq]; exact peelLvl_eq_run _ _ _ _ _ _ _ _ _ h

theorem defeqPeel_leaf_run (r : CoreFnsA) (d peel : Nat) (a b : EIdx) (k : Nat) (fvs : Array EIdx)
    (s : AState) (h : (a == b) = false)
    (hl : (decide (peel = 0) || a.tag != ETag.forallE || b.tag != ETag.forallE) = true) :
    (defeqPeel r d peel a b k fvs).run s = (defeqPeelLeaf r d a b k fvs).run s := by
  cases peel with
  | zero => rw [defeqPeel_zero_eq]; exact peelLvl_leaf_run _ _ _ _ _ _ _ _ _ h hl
  | succ p => rw [defeqPeel_succ_eq]; exact peelLvl_leaf_run _ _ _ _ _ _ _ _ _ h hl

theorem word_toNat_zero_iff (w : Word) : w.toNat = 0 ↔ w = 0 :=
  ⟨fun h => UInt64.toNat_inj.mp (by simpa using h), fun h => by rw [h]; rfl⟩

section loopRef
variable (p : Prog) (hp : PeelProg p) (hil : InstListOK p)

include hp hil in
/-- **The descent refines `defeqPeel`, both outcomes**, at the knot. -/
theorem peel_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (mode d fo : Word)
    (hmode : mode < 4) :
    ∀ j, j ≤ n + 1 → ∀ (peel a b k : Word) (m : Mem) (s : AState) (M : ModeMaps) (eb : Word)
      (fvs : Array EIdx), CoreS dn m s vis fe M eb → eb = (mode >>> 1) &&& 1 → HW a → HW b →
      FvsR m fo k fvs → d.toNat + k.toNat + peel.toNat < 2 ^ 64 →
      RefE (PeelG p n) (peelE.loop1 p j m mode vis d peel a b k fo)
        (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE a) (decE b)
          k.toNat fvs) s
        (fun v y a' => GrowPost decBool dn m vis fe M eb ResH ([v.1], v.2) y a') := by
  intro j
  induction j with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    unfold peelE.loop1; exact RefE.of_cls0 rfl
  | succ j ih =>
    intro hjn peel a b k m s M eb fvs hS heb ha hb hx hdk
    have hab : (decE a == decE b) = decide (a = b) := decE_beq_eq _ _ ha hb
    by_cases he : a = b
    · rw [peelE.loop1.arm1 (hc1 := rfl) (hc2 := he)]
      have hr := defeqPeel_eq_run (coreKnot (decMode mode) fe id F) d.toNat peel.toNat _ _ k.toNat
        fvs s (by rw [hab]; simp [he])
      exact RefE.ret hr (GrowPost.of_core (CorePost.ret hS rfl resH_one))
    have hab' : (decE a == decE b) = false := by rw [hab]; simp [he]
    have hlw : (decide (peel.toNat = 0) || (decE a).tag != ETag.forallE ||
        (decE b).tag != ETag.forallE) = decide (peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6) := by
      simp only [bne, decE_tag_forallE_beq a ha, decE_tag_forallE_beq b hb, word_toNat_zero_iff]
      by_cases h1 : peel = 0 <;> by_cases h2 : a >>> 28 = 6 <;> by_cases h3 : b >>> 28 = 6 <;>
        simp [h1, h2, h3]
    by_cases hl : peel = 0 ∨ a >>> 28 ≠ 6 ∨ b >>> 28 ≠ 6
    · rw [peelE.loop1.arm2 (hc1 := rfl) (hc2 := he) (hc3 := hl)]
      have hr := defeqPeel_leaf_run (coreKnot (decMode mode) fe id F) d.toNat peel.toNat _ _ k.toNat
        fvs s hab' (by rw [hlw]; simp [hl])
      refine RefE.of_run_eq hr ?_
      rcases h1 : callE p j "peel_leaf" [mode, vis, d, a, b, k, fo] m with e | ⟨r, m₁⟩
      · rw [peelE.k_peel_leaf.none]
        cases j with
        | zero =>
          obtain ⟨e', he', h0⟩ := callE_zero p "peel_leaf" [mode, vis, d, a, b, k, fo] m
          rw [h1] at he'; cases he'; exact RefE.of_cls0 h0
        | succ j' =>
        exact fun hG => RefE.run_err (plE_spec p hp.leaf (j' + 1) ⟨m, Locals.init []⟩ mode vis d a b k fo)
          hG.nv (hG.knot.mono (by omega)) (pl_ref p hil j' (hk.mono (by omega)) F (by omega) (by omega)
            _ s dn vis fe M eb mode d a b k fo ⟨hS, hmode, heb⟩ ha hb fvs hx (by omega)) h1
      obtain ⟨j', rfl⟩ := callW_succ (callW_of_callE h1)
      simp only [peelE.k_peel_leaf]
      obtain ⟨hrun, hR⟩ := (CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
        (peelLeaf_refines p hp hil j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb
          mode d a b k fo ⟨hS, hmode, heb⟩ ha hb fvs hx (by omega)) (callW_of_callE h1)).post
      exact RefE.ret hrun (GrowPost.of_core ⟨hR.after, by simpa [decBool] using hR.res, hR.valid⟩)
    have hp0 : peel ≠ 0 := fun h0 => hl (.inl h0)
    have hga : a >>> 28 = 6 := Classical.byContradiction fun h' => hl (.inr (.inl h'))
    have hgb : b >>> 28 = 6 := Classical.byContradiction fun h' => hl (.inr (.inr h'))
    obtain ⟨q, hq⟩ : ∃ q, peel.toNat = q + 1 :=
      ⟨peel.toNat - 1, by have : peel.toNat ≠ 0 := fun h0' => hp0 ((word_toNat_zero_iff peel).mp h0'); omega⟩
    have hq1 : (peel - 1).toNat = q := by
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp; omega
    have hk1 : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
    rw [peelE.loop1.arm3 (hc1 := rfl) (hc2 := he) (hc3 := hl)]
    have hr := defeqPeel_succ_eq (coreKnot (decMode mode) fe id F) d.toNat q (decE a) (decE b)
      k.toNat fvs
    have hl' : (decide (q + 1 = 0) || (decE a).tag != ETag.forallE ||
        (decE b).tag != ETag.forallE) = false := by rw [← hq, hlw]; simp [hl]
    rw [hq]
    refine RefE.of_run_eq ((congrArg (fun T => StateT.run T s) hr).trans
      (peelLvl_step_run _ _ _ _ _ _ _ _ _ hab' hl')) ?_
    rcases hc : callE p j "peel_step" [mode, vis, d, a, b, k, fo] m with e | ⟨r₁, m₁⟩
    · rw [peelE.k_peel_step.none]
      cases j with
      | zero =>
        obtain ⟨e', he', h0⟩ := callE_zero p "peel_step" [mode, vis, d, a, b, k, fo] m
        rw [hc] at he'; cases he'; exact RefE.of_cls0 h0
      | succ j' =>
      exact RefE.bind_left fun hG => RefE.run_err
        (psE_spec p hp.step hp.step2 hp.dom (j' + 1) ⟨m, Locals.init []⟩ mode vis d a b k fo) hG.nv
        (hG.knot.mono (by omega)) (ps_ref p hp hil j' (hk.mono (by omega)) F (by omega) (by omega)
          _ s dn vis fe M eb mode d a b k fo ⟨hS, hmode, heb⟩ ha hb hga hgb fvs hx (by omega)) hc
    obtain ⟨j', rfl⟩ := callW_succ (callW_of_callE hc)
    have e₁ := CoreSpec.of_callW (s₀ := ⟨m, Locals.init []⟩)
      (peelStep_refines p hp hil j' (hk.mono (by omega)) F (by omega) (by omega) _ s dn vis fe M eb
        mode d a b k fo ⟨hS, hmode, heb⟩ ha hb hga hgb fvs hx (by omega)) (callW_of_callE hc)
    refine RefE.bind_growK (w := fun (v : Word × Mem) => ([v.1], v.2)) e₁ (fun M₁ hS₁ hst₁ => ?_)
    obtain ⟨hw0, hw1, hw2, hw3⟩ := e₁.2.2.2
    by_cases h0 : r₁.headD 0 = 0
    · rw [peelE.k_peel_step.arm1 (hc1 := h0)]
      simp only [decPS, h0, bne_self_eq_false, Bool.not_false, ↓reduceIte]
      exact RefE.ret rfl (GrowPost.of_core (CorePost.ret hS₁ rfl resH_zero))
    rw [peelE.k_peel_step.arm2 (hc1 := h0)]
    have hnz : (r₁.headD 0 != 0) = true := by simpa using h0
    simp only [decPS, hnz, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    rcases hc2 : callE p (j' + 1) "peel_push" [d, k, fo, r₁.tail.headD 0] m₁ with e | ⟨r₂, m₂⟩
    · rw [peelE.k_peel_push.none]
      exact fun hG => ErrClaim.of_cls0
        (callE_nv hG.nv (_root_.L.Checker.nv_mem (by decide +kernel)) _ _ _ hc2)
    rw [peelE.k_peel_push.arm1]
    obtain ⟨e₂, hx₂⟩ := peelPush_run hp hS₁ d k fo _ hw1 fvs (hx.kept hst₁ hS.spn)
      (by omega) r₂ (callW_of_callE hc2)
    refine RefE.bind_grow (w := fun (v : Word × Mem) => ([v.1], v.2)) e₂ (fun M₂ hS₂ _ => ?_)
    have := ih (by omega) (peel - 1) _ _ (k + 1) m₂ _ M₂ eb _ hS₂ heb hw2 hw3 hx₂
      (by rw [hq1, hk1]; omega)
    rw [hq1, hk1] at this
    exact this

include hp hil in
/-- `defeq_peel` from its run, both outcomes (`peel_ref` at the call's fuel). -/
theorem defeqPeel_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb mode d peel a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (ha : HW a) (hb : HW b) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64) :
    RefE (PeelG p n) (peelE p (n + 1) s₀.mem mode vis d peel a b k fo)
      (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat peel.toNat (decE a) (decE b) k.toNat fvs) a₀
      (fun v y a' => GrowPost decBool dn s₀.mem vis fe M eb ResH ([v.1], v.2) y a') := by
  rw [peelE.arm1]
  exact peel_ref p hp hil n hk F hF hn dn vis fe mode d fo hs.mode4 (n + 1) (Nat.le_refl _) peel a b k
    s₀.mem a₀ M eb fvs hs.rel hs.eb_mode ha hb hx hdk

end loopRef

/-- **`defeq_peel` refines `defeqPeel`** at the knot: the slice `fvs = (fo, k)` at the top of the
stack, the result's stack grown (`defeqPeel_ref`'s ok half). -/
@[refines ConRon.Arena.defeqPeel]
theorem defeqPeel_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d peel a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat + peel.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "defeq_peel" [mode, vis, d, peel, a, b, k, fo]
    ⦃fun r s' => LocEq s' s₀ ∧ GrowRefP (defeqPeel (coreKnot (decMode mode) fe id F) d.toNat
      peel.toNat (decE a) (decE b) k.toNat fvs) a₀ decBool dn s₀.mem vis fe M eb r s'.mem; ⊤⦄ := by
  refine L.M.triple_of_run fun _ r s' hp0 hr => ?_
  obtain ⟨hl, y, a', hrun, hR⟩ := L.M.of_run (P := fun s => s = s₀) hp0 hr
    (RefE.triple (defeqPeel_specE p hp.peel (n + 1) s₀ mode vis d peel a b k fo)
      (defeqPeel_ref p hp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d peel a b k fo hs ha hb fvs hx
        hdk))
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hl, hok, hst ▸ hR.after, hres ▸ hR.res.trans (by simp [decBool]), hR.valid⟩

/-! ## `defeq_binders` -/

/-- **`defeq_binders`' model, both outcomes** (generated; the `defeq` slot and `defeq_peel` through
their runs, `peel_push` lifted). -/
l_model dbE_spec (p : Prog) (hf : p.lookup "defeq_binders" = some defeqBindersL)
  fns [hf ↦ dbE list]
  specs [callW_spec p n "peel_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- A run of `peel_push` wrote inside the stack array. -/
theorem peelPush_bound {p : Prog} (hp : PeelProg p) {n : Nat} {m m' : Mem} (d k fo t2 : Word)
    {r : List Word} (hc : callW p (n + 1) "peel_push" [d, k, fo, t2] m = some (r, m')) :
    (fo + k).toNat < (m.arr64 SPN).size := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (peelPush_spec p hp n ⟨m, Locals.init []⟩ d k fo t2) hc
  cases hc1 : callW p n "intern_fvar" [d + k, t2] m with
  | none => rw [hc1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [hc1] at hW
  obtain ⟨s'', rfl, -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internFVar_spec p hp.fvf hp.fvp hp.fvi n ⟨m, Locals.init []⟩ (d + k) t2) hc1
  have hsz : (s''.mem.arr64 SPN).size = (m.arr64 SPN).size :=
    (fvinternW_frame _ _ _ _ _ hI).size SPN
  simp only [peelPushK] at hW
  split at hW
  · rename_i hb; rw [← hsz]; exact hb.1
  · cases hW

theorem fvsR_empty {m : Mem} {so : Word} (htop : spTop m = so) (hb : so.toNat < (m.arr64 SPN).size)
    (hspn : (m.arr64 SPN).size < 2 ^ 63) : FvsR m so 0 #[] :=
  ⟨⟨rfl, by simp; omega, fun i hi => by simp at hi, fun i hi => by simp at hi⟩,
    by rw [htop]; simp, by simp; omega⟩

/-- **`defeq_binders` refines `defeqBinders`, both outcomes** (the depth leaves room for the peel's
budget): the errors are the `defeq` slot's and the descent's. -/
theorem db_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty1 body1 ty2 body2 : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h1 : HW ty1) (hb1 : HW body1) (h2 : HW ty2) (hb2 : HW body2)
    (hd : d.toNat + 1 + peelFuel < 2 ^ 64) :
    RefE (PeelG p n) (dbE p (n + 1) s₀.mem mode vis d ty1 body1 ty2 body2)
      (defeqBinders (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1) (decE ty2)
        (decE body2)) a₀ (CorePost decBool dn s₀.mem vis fe M eb ResH) := by
  simp only [dbE]
  unfold defeqBinders
  rcases c1 : callE p n "defeq" [mode, vis, d, ty1, ty2] s₀.mem with e | ⟨r₁, m₁⟩
  · exact fun hG => ErrClaim.bind_left (CoreSpecE.of_callE
      ((hG.knot n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty1 ty2 hF hn hs h1 h2) c1)
  have e₁ := CoreSpec.of_callW
    ((hk n (Nat.le_refl _)).defeq F s₀ a₀ dn vis fe M eb mode d ty1 ty2 hF hn hs h1 h2)
    (callW_of_callE c1)
  simp only [dbE.k_defeq]
  refine RefE.bind_core (w := id) e₁ (fun M₁ hS₁ hst₁ => ?_)
  by_cases h0 : r₁.headD 0 = 0
  · rw [ite_eq_left h0, decBool_f h0]
    exact RefE.ret rfl (CorePost.ret hS₁ rfl resH_zero)
  rw [ite_eq_right h0, decBool_t h0]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hso : rdW (m₁.arr64 CTL) 136 = spTop m₁ := rfl
  rw [hso]
  rcases c2 : callW p n "peel_push" [d, 0, spTop m₁, ty2] m₁ with _ | ⟨r₂, m₂⟩
  · rw [liftE_none, dbE.k_peel_push.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [dbE.k_peel_push]
  obtain ⟨n', rfl⟩ := callW_succ c2
  have hbnd := peelPush_bound hp d 0 (spTop m₁) ty2 c2
  rw [UInt64.add_zero] at hbnd
  obtain ⟨e₂, hx₂⟩ := peelPush_run hp hS₁ d 0 (spTop m₁) ty2 h2 #[]
    (fvsR_empty rfl hbnd hS₁.spn) (by rw [toNat_zero_w, Nat.add_zero]; omega) r₂ c2
  have e0 : d.toNat + (0 : Word).toNat = d.toNat := rfl
  rw [e0] at e₂
  rw [UInt64.zero_add] at hx₂
  have e1 : (16777216 : Word).toNat = peelFuel := by simp [peelFuel]
  have e2 : (1 : Word).toNat = 1 := rfl
  have e3 : (#[] : Array EIdx).push (decE (r₂.headD 0)) = #[decE (r₂.headD 0)] := rfl
  have hdk' : d.toNat + (1 : Word).toNat + (16777216 : Word).toNat < 2 ^ 64 := by
    rw [e1, e2]; exact hd
  rcases c3 : callE p (n' + 1) "defeq_peel"
      [mode, vis, d, 16777216, body1, body2, 1, spTop m₁] m₂ with e | ⟨r₃, m₃⟩
  · intro hG
    obtain ⟨M₂, hS₂, -, -⟩ := e₂.2.1
    refine ErrClaim.bind_right (by rw [AM.run_of_ok _ _ e₂.1, e₂.2.2.1]) ?_
    have := RefE.run_err (defeqPeel_specE p hp.peel (n' + 1) ⟨m₂, Locals.init []⟩ mode vis d
        16777216 body1 body2 1 (spTop m₁)) trivial (hG.mono (by omega))
      (defeqPeel_ref p hp hil n' (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩
        _ dn vis fe M₂ eb mode d 16777216 body1 body2 1 (spTop m₁) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb1 hb2
        _ hx₂ hdk') c3
    rwa [e1, e2, e3] at this
  simp only [dbE.k_defeq_peel]
  have hG : GrowRefP (internFVarE d.toNat (decE ty2) >>= fun fv => defeqPeel (coreKnot (decMode mode)
      fe id F) d.toNat peelFuel (decE body1) (decE body2) 1 #[fv]) _ decBool dn m₁ vis fe M₁ eb r₃ m₃ :=
    growRef_bind e₂ (fun M₂ hS₂ _ => by
    obtain ⟨t, ht, -, hP⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
      (defeqPeel_refines p hp hil n' (hk.mono (by omega)) F (by omega) (by omega) ⟨m₂, Locals.init []⟩
        _ dn vis fe M₂ eb mode d 16777216 body1 body2 1 (spTop m₁) ⟨hS₂, hs.mode4, hs.eb_mode⟩ hb1 hb2
        _ hx₂ hdk') (callW_of_callE c3)
    rw [ht, e1, e2, e3] at hP
    exact hP)
  obtain ⟨hok, hA, hres, hr⟩ := hG
  exact RefE.ret (AM.run_of_ok _ _ hok) (GrowPost.restore (m₀ := m₁) ⟨hA, hres, hr⟩ [r₃.headD 0]
    (by simp only [decBool, List.headD_cons]) hr)

/-- **`defeq_binders` refines `defeqBinders`** at the knot (`db_ref`'s ok half). -/
@[refines ConRon.Arena.defeqBinders]
theorem defeqBinders_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d ty1 body1 ty2 body2 : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode)
    (h1 : HW ty1) (hb1 : HW body1) (h2 : HW ty2) (hb2 : HW body2)
    (hd : d.toNat + 1 + peelFuel < 2 ^ 64) :
    CoreSpec p (n + 1) "defeq_binders" [mode, vis, d, ty1, body1, ty2, body2]
      (defeqBinders (coreKnot (decMode mode) fe id F) d.toNat (decE ty1) (decE body1) (decE ty2)
        (decE body2)) decBool s₀ a₀ dn vis fe M eb :=
  RefE.coreSpec (dbE_spec p hp.binders (n + 1) s₀ mode vis d ty1 body1 ty2 body2)
    (db_ref p hp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d ty1 body1 ty2 body2 hs h1 hb1 h2 hb2 hd)

end L.Arena
