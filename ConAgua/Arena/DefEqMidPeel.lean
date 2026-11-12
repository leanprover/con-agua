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

/-! ## `peel_leaf` -/

/-- **`peel_leaf`'s model, both outcomes** (generated; `inst_list` lifted, the `defeq` slot through
its run). -/
l_model plE_spec (p : Prog) (hf : p.lookup "peel_leaf" = some peelLeafL)
  fns [hf ↦ plE list]
  specs [callW_spec p n "inst_list"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
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

theorem toNat_zero_w : (0 : Word).toNat = 0 := rfl

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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`peel_dom` refines `peelDomT` (one level's domains), both outcomes**: the errors are the
`defeq` slot's. -/
theorem pd_ref (p : Prog) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da db k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW da) (hb : HW db)
    (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs) (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (pdE p (n + 1) s₀.mem mode vis d da db k fo)
      (peelDomT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE da) (decE db) k.toNat fvs) a₀
      (CorePost decDom dn s₀.mem vis fe M eb ResW) := by
  simp only [pdE]
  unfold peelDomT
  rw [← L.toNat_add_of_lt d k hdk]
  refine RefE.bind_callW (fun _ => rfl) (hil n s₀ a₀ dn vis fe M eb da fo k 0 fvs hs.rel ha hx.spine
    hx.le_top) fun r₁ m₁ _ e₁ => RefE.after_core (w := id) e₁ fun M₁ hS₁ hst₁ => ?_
  dsimp only [pdE.k_inst_list]
  by_cases he : da = db
  · have hbq : (decE da == decE db) = true := by rw [he]; exact beq_self_eq_true _
    rw [ite_eq_left he]
    simp only [hbq, ↓reduceIte, pure_bind]
    exact RefE.ret rfl (CorePost.ret hS₁ (by simp only [decDom, decH]; rfl) ⟨hw1, e₁.resOk⟩)
  rw [ite_eq_right he]
  have hbq : (decE da == decE db) = false := by
    rw [decE_beq_eq _ _ ha hb]; simp [he]
  simp only [hbq, Bool.false_eq_true, ↓reduceIte]
  have hx₁ := hx.kept hst₁ hs.rel.spn
  refine RefE.bind_callW (fun _ => rfl) (hil n ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb db fo k 0 fvs hS₁ hb
    hx₁.spine hx₁.le_top) fun r₂ m₂ _ e₂ => RefE.after_core (w := id) e₂ fun M₂ hS₂ _ => ?_
  dsimp only [pdE.k_inst_list_2]
  have hs₂ : SlotPre ⟨m₂, Locals.init []⟩ _ dn vis fe M₂ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (fun _ => rfl) ((hk n (Nat.le_refl _)).defeq F _ _ dn vis fe M₂ eb mode (d + k)
    _ _ hF hn hs₂ e₁.resOk e₂.resOk) (fun (hG : KnotUpToE p n) => (hG n (Nat.le_refl _)).defeq F _ _ dn
      vis fe M₂ eb mode (d + k) _ _ hF hn hs₂ e₁.resOk e₂.resOk)
    fun r₃ m₃ _ e₃ => RefE.after_core (w := id) e₃ fun M₃ hS₃ _ => ?_
  exact RefE.ret rfl (CorePost.ret hS₃ (by simp only [decDom, decBool, decH]; rfl)
    ⟨e₃.resOk, e₂.resOk⟩)

/-! ## `e_view` runs -/

/-- **A run of `e_view` at a `∀`**: the memory kept, the binder's two words, the twin's
`viewBind`. -/
theorem eView_forall_callW {p : Prog} (hp : p.lookup "e_view" = some L.Ind.eView) {n : Nat}
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : tagW h = 6)
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
    {m m' : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : HW h) (hg : tagW h = 5)
    {r : List Word} (hc : callW p n "e_view" [h] m = some (r, m')) :
    m' = m ∧ HW (r.tail.headD 0) ∧ HW (r.tail.tail.headD 0) ∧
      a.store.viewBind (decE h) = some (decE (r.tail.headD 0), decE (r.tail.tail.headD 0)) := by
  obtain ⟨s', hm, rfl, hne, hr⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.eView_spec p hp n ⟨m, Locals.init []⟩ h) hc
  obtain ⟨hv, hw⟩ := L.Ind.eViewW_lam m h hg (hr ▸ hne)
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
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`peel_step2` refines `peelStep2T`, both outcomes**, at a `∀` handle `b`: the errors are
`peel_dom`'s. -/
theorem ps2_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d da b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (hda : HW da) (hb : HW b)
    (hg : tagW b = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (ps2E p (n + 1) s₀.mem mode vis d da b k fo)
      (peelStep2T (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs) a₀
      (CorePost decPS2 dn s₀.mem vis fe M eb Res3') := by
  simp only [ps2E]
  rcases c1 : callW p n "e_view" [b] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, ps2E.k_e_view.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [ps2E.k_e_view]
  obtain ⟨k', rfl⟩ := callW_succ c1
  obtain ⟨rfl, -, -, hw1, hw2, hvb⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.base hb hg c1
  have hT : (peelStep2T (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE da) (decE b) k.toNat fvs).run a₀ =
      (peelDomT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE da) (decE (r₁.tail.headD 0)) k.toNat fvs
        >>= fun x => pure (x.1, x.2, decE (r₁.tail.tail.headD 0))).run a₀ := by
    simp only [peelStep2T, StateT.run_bind, L.Arena.viewBind_run, hvb, except_ok_bind]
  refine RefE.of_run_eq hT ?_
  have H := pd_ref p hil k' (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
    mode d da _ k fo hs hda hw1 fvs hx hdk
  exact RefE.tailMap_pure (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (by omega))
    (fun _ _ _ hP => ⟨hP.after, by rw [hP.res]; rfl, ⟨hP.valid.1, hP.valid.2, hw2⟩⟩) H

/-- **`peel_step`'s model, both outcomes** (generated; `e_view` lifted, `peel_step2` by its unified
model). -/
l_model psE_spec (p : Prog) (hf : p.lookup "peel_step" = some peelStepL)
    (h2 : p.lookup "peel_step2" = some peelStep2L) (hd : p.lookup "peel_dom" = some peelDomL)
  fns [hf ↦ psE list]
  specs [callW_spec p n "e_view", ps2E_spec p h2 hd n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`peel_step` refines `peelStepT`, both outcomes**, at two `∀` handles: the errors are
`peel_step2`'s. -/
theorem ps_ref (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hga : tagW a = 6) (hgb : tagW b = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    RefE (KnotUpToE p n) (psE p (n + 1) s₀.mem mode vis d a b k fo)
      (peelStepT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs) a₀
      (CorePost decPS dn s₀.mem vis fe M eb Res4) := by
  simp only [psE]
  rcases c1 : callW p n "e_view" [a] s₀.mem with _ | ⟨r₁, m₁⟩
  · rw [liftE_none, psE.k_e_view.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]; simp only [psE.k_e_view]
  obtain ⟨k', rfl⟩ := callW_succ c1
  obtain ⟨rfl, -, -, hw1, hw2, hva⟩ := eView_forall_callW (a := a₀) hp.eview hs.rel.arena.base ha hga c1
  have hT : (peelStepT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs).run a₀ =
      (peelStep2T (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE (r₁.tail.headD 0)) (decE b) k.toNat fvs
        >>= fun y => pure (y.1, y.2.1, decE (r₁.tail.tail.headD 0), y.2.2)).run a₀ := by
    simp only [peelStepT, StateT.run_bind, L.Arena.viewBind_run, hva, except_ok_bind]
  refine RefE.of_run_eq hT ?_
  have H := ps2_ref p hp hil k' (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis fe M eb
    mode d _ b k fo hs hw1 hb hgb fvs hx hdk
  exact RefE.tailMap_pure (fun _ => rfl) (fun _ => rfl) (fun hkE => hkE.mono (by omega))
    (fun _ _ _ hP => ⟨hP.after, by rw [hP.res]; rfl, ⟨hP.valid.1, hP.valid.2.1, hw2, hP.valid.2.2⟩⟩) H

/-- **`peel_step` refines `peelStepT`** at two `∀` handles (`ps_ref`'s ok half). -/
theorem peelStep_refines (p : Prog) (hp : PeelProg p) (hil : InstListOK p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d a b k fo : Word) (hs : SlotPre s₀ a₀ dn vis fe M eb mode) (ha : HW a) (hb : HW b)
    (hga : tagW a = 6) (hgb : tagW b = 6) (fvs : Array EIdx) (hx : FvsR s₀.mem fo k fvs)
    (hdk : d.toNat + k.toNat < 2 ^ 64) :
    CoreSpec p (n + 1) "peel_step" [mode, vis, d, a, b, k, fo]
      (peelStepT (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE a) (decE b) k.toNat fvs)
      decPS s₀ a₀ dn vis fe M eb Res4 :=
  RefE.coreSpec (psE_spec p hp.step hp.step2 hp.dom (n + 1) s₀ mode vis d a b k fo)
    (ps_ref p hp hil n hk F hF hn s₀ a₀ dn vis fe M eb mode d a b k fo hs ha hb hga hgb fvs hx hdk)

/-! ## `peel_push` -/

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
    vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, st64, callW_spec p n "intern_fvar"] <;>
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
    rw [L.toNat_add_of_lt d k hdk] at e₁
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
      rw [L.Arena.rdW_set64, ite_eq_left ⟨rfl, rfl, by rw [L.Mem.size64_set64]; exact hb2⟩]
    have hk1' : (k + 1).toNat = k.toNat + 1 := by
      rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; have := hx.fit; omega
    refine ⟨⟨hok, ⟨M₁, hS₂, hK₁, ?_⟩, by rw [hres, decH, hr]; rfl, by unfold ResH; rw [← hr]; exact hw⟩,
      ⟨by rw [← hr]; exact hpush.of_spn hspn', by rw [htop, UInt64.add_assoc], by rw [hk1']; omega⟩⟩
    -- the stack grew
    have hsz : (s'.mem.arr64 SPN).size = (m.arr64 SPN).size := by
      rw [hspn', L.Mem.size64_set64]; exact hst₁.size
    refine ⟨?_, hsz, fun i hi => ?_, hst₁.bstk.trans (BKept.of_frame hfr (by decide) (by decide)),
      hst₁.pool.trans (PoolGrew.of_frame hfr (by decide) (by decide))⟩
    · rw [htop, hx.top, UInt64.le_iff_toNat_le]
      simp only [UInt64.toNat_add, UInt64.toNat_one]
      have := hx.fit; omega
    · have hi' : i ≠ fo + k := fun h => by rw [h, ← hx.top] at hi; exact absurd hi (by simp)
      unfold spW
      rw [hspn', L.Arena.rdW_set64, ite_eq_right (fun h => hi' h.2.1.symm)]
      exact hst₁.below i hi
  · cases hW

/-! ## The twin's descent, one level at a time -/

theorem viewBind_bind_run {β : Type} (h : EIdx) (f : Option (EIdx × EIdx) → AM β) (s : AState) :
    (viewBind h >>= f).run s = (f (s.store.viewBind h)).run s := by
  simp only [StateT.run_bind, L.Arena.viewBind_run, except_ok_bind]

/-! ## `defeq_peel`: the loop -/

/-- **`defeq_peel`'s model, both outcomes** (the loop `peelE.loop1`: `peel_leaf`, `peel_step`,
`peel_push` through their runs, `callE`). -/
l_model defeqPeel_specE (p : Prog) (hf : p.lookup "defeq_peel" = some defeqPeelL)
  fns [hf ↦ peelE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

/-! ## The loop refines `defeqPeel` -/

theorem word_toNat_zero_iff (w : Word) : w.toNat = 0 ↔ w = 0 :=
  ⟨fun h => UInt64.toNat_inj.mp (by simpa using h), fun h => by rw [h]; rfl⟩

section loopRef
variable (p : Prog) (hp : PeelProg p) (hil : InstListOK p)

include hp hil in

/-! ## `defeq_binders` -/

/-- **`defeq_binders`' model, both outcomes** (generated; the `defeq` slot and `defeq_peel` through
their runs, `peel_push` lifted). -/
l_model dbE_spec (p : Prog) (hf : p.lookup "defeq_binders" = some defeqBindersL)
  fns [hf ↦ dbE list]
  specs [callW_spec p n "peel_push"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
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

end loopRef

end L.Arena
