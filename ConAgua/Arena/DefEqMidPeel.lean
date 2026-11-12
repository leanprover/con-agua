module

public import ConAgua.Arena.DefEqMid
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.Arena.DerRel
import ConAgua.Arena.RefWalk
import ConAgua.Arena.StripTeleSpec
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Checker.NoVerdictTree
import ConAgua.Front.Preserve
import ConAgua.L.ModelGen
public import ConAgua.Arena.IndView
import all ConAgua.Arena.DefEq
import ConAgua.L.WordOff
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.Inst1Refine

@[expose] public section

/-!
# The binder-telescope congruence: `defeq_binders` (lane `defeq`)

`defeq_binders` (`DefEq.lean`) is the twin's `defeqBinders`: per level `inst_list` of the right
domain over the variable slice, `defeq_domain`, the fresh variable pushed at the stack top, then
`binder_pair` and the next level, or `defeq_binders_inner` at the innermost one. `fvs` is the stack
slice `(fo, k)` with the top at `fo + k` (`FvsR`); a push grows it, so the post is `GrowPost`
(the stack below the old top kept, the top grown); `quick_binders` puts the top back.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- The lookups of this file. -/
structure PeelProg (p : Prog) : Prop where
  domain : p.lookup "defeq_domain" = some defeqDomainL
  inner : p.lookup "defeq_binders_inner" = some defeqBindersInnerL
  pair : p.lookup "binder_pair" = some binderPairL
  binders : p.lookup "defeq_binders" = some defeqBindersL
  eview : p.lookup "e_view" = some L.Ind.eView
  fvf : p.lookup "fvar_find" = some fvarFind
  fvp : p.lookup "fvar_push" = some fvarPush
  fvi : p.lookup "intern_fvar" = some internFVar

/-! ## `intern_fvar` under `CoreS` -/

theorem fvinternW_hw (m : Mem) (a : AState) (hR : FVarR m a) (u ty w : Word) (m' : Mem)
    (hI : fvinternW m u ty = some (w, m')) : HW w := by
  exact consInternM_lt fvarCS_wf hR hI

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
    hS.arena_frame hD (Keeps.run (L.Arena.keeps_cpl_internFVar _ _) hrun) hf
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
    by rw [hres]; rfl, fvinternW_hw m a hS.arena.base.fvar u ty _ _ hI⟩, hf⟩

/-! ## Growing runs

`WhnfCoreProj.lean`'s `GrowRefP` with its lemmas, restated here (that file and `DefEqLeaves.lean`
both defined `lsNodeW_viewLen`, so they could not be imported together; DefEqLeaves' copy is now `defeq_lsNodeW_viewLen`). -/

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
  exact ⟨hok, hst ▸ ⟨M'', hS'', hK.trans hK'', hSt.trans hSt''⟩, hres.trans hres2, hrw2⟩

/-! ## The variable slice -/

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

theorem toNat_zero_w : (0 : Word).toNat = 0 := rfl

/-! ## `defeq_domain`, `binder_pair`, `defeq_binders` -/

/-- **`defeq_domain`'s model, both outcomes** (generated; `inst_list` lifted, the `defeq` slot
through its run). -/
l_model ddE_spec (p : Prog) (hf : p.lookup "defeq_domain" = some defeqDomainL)
  fns [hf ↦ ddE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`defeq_binders`' model, both outcomes** (generated; recursive; `inst_list`, `intern_fvar`,
`binder_pair` lifted, `defeq_domain` and `defeq_binders_inner` by their models). -/
l_model dbE_spec (p : Prog) (hp : PeelProg p)
  fns [hp.binders ↦ dbE list]
  specs [callW_spec p n "inst_list", ddE_spec p hp.domain n, callW_spec p n "intern_fvar",
    callW_spec p n "binder_pair", liE_spec p hp.inner n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`defeq_binders` refines `defeqBinders`, both outcomes** (the variable slice `fvs` at the stack
top; the depth leaves room for the budget): the errors are the slots' and `inst_list`'s. -/
theorem db_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode lam fuel d fo k ty1 body1 ty2 body2 : Word) (fvs : Array EIdx)
    (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hx : FvsR s₀.mem fo k fvs)
    (h1 : HW ty1) (hb1 : HW body1) (h2 : HW ty2) (hb2 : HW body2)
    (hd : d.toNat + fuel.toNat + 1 < 2 ^ 64) :
    RefE (KnotNvG p n) (dbE p (n + 1) s₀.mem mode vis lam fuel d fo k ty1 body1 ty2 body2)
      (defeqBinders (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) (lam != 0)
        fuel.toNat d.toNat fvs (decE ty1) (decE body1) (decE ty2) (decE body2)) a₀
      (GrowPost decBool dn s₀.mem vis fe M eb ResH) := by
  sorry

