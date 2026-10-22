import ConAgua.Arena.WhnfCoreStep

/-!
# Refinements of `WhnfCore.lean`'s projection functions

`proj_lit_to_ctor`, `whnf_core_step_proj`, `reduce_proj_core` (`WhnfCore.lean`), by the
`WhnfCoreRefine.lean`/`WhnfCoreSlot.lean` method: a word-level model whose callees are `callW`
runs, the L spec by `vcgen` + `finish`, then the refinement by case analysis on the model, each
callee's spec applied to its run, and the post `CoreRef` built by `refine ⟨hok, ?_, ?_, ?_⟩`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `proj_lit_to_ctor` -/

/-- The model of `proj_lit_to_ctor`: not a `lit` handle, or a `natVal` one, answers it unchanged;
a `strVal` one, unsupported, answers it unchanged; else the reduced constructor form. -/
def projLitToCtorW (p : Prog) (n : Nat) (m : Mem) (mode vis d h : Word) : Option (Word × Mem) :=
  if h >>> 28 ≠ 8 then some (h, m)
  else if tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) (2 + tierW h) ≤ idxW h then none
  else if rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 1 then some (h, m)
  else match callW p n "str_lit_supported" [vis] m with
    | none => none
    | some (r₁, m₁) =>
      if r₁.headD 0 = 0 then some (h, m₁)
      else match callW p n "str_lit_ctor" [h] m₁ with
        | none => none
        | some (r₂, m₂) =>
          match callW p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with
          | none => none
          | some (r₃, m₃) => some (r₃.headD 0, m₃)

theorem projLitToCtor_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St)
    (mode vis d h : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_lit_to_ctor" [mode, vis, d, h]
    ⦃fun r s' => LocEq s' s₀ ∧
      projLitToCtorW p n s₀.mem mode vis d h = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.plit]
  simp only [callFn, projLitToCtorL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "str_lit_supported", callW_spec p n "str_lit_ctor", callW_spec p n "whnf"] <;>
    finish [projLitToCtorW, viewOK, tierW, idxW]

/-! ## Handle-word lemmas: the `lit` tag, and the kind word says `natVal`/`strVal` -/

theorem decE_lit_tag (h : Word) (hh : HW h) : ((decE h).tag == ETag.lit) = (h >>> 28 == 8) := by
  rw [decE_tag h hh, ETag.lit]
  rw [show (8 : UInt32) = (8 : Word).toUInt32 from rfl]
  exact toUInt32_beq _ _ (shr28_lt h hh) (by decide)

/-- **Under `ArenaR`, on a `lit` node past the view checks, the kind word says whether the
literal is a `strVal`** (the converse direction of `view_lit`, exposing the kind word). -/
theorem view_lit_kind (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 2) (hg : h >>> 28 = 8) :
    (rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) = 1 →
      ∃ s, a.store.view (decE h) = some (.lit (.strVal s))) ∧
    (rdW (m.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 1 →
      ∃ l, a.store.view (decE h) = some (.lit l) ∧ ∀ s, l ≠ .strVal s) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litSch RecRel litH (·.lits) _ hR.lit.2 hv.2
  have hview : ∀ l, k = ⟨l⟩ → a.store.view (decE h) = some (.lit l) := by
    intro l hl
    rw [view_tier m a hR h hh hv.1, get_lit _ h hh hg, Tbl.node?, hk, hl]
    rfl
  obtain ⟨⟨N⟩ | ⟨s⟩⟩ := k
  · refine ⟨fun hcontra => ?_, fun _ => ⟨.natVal N, hview _ rfl, fun s hs => by cases hs⟩⟩
    exfalso
    simp only [RecRel_natVal, NatRec] at hkr
    exact absurd (hkr.1.symm.trans hcontra) (by decide)
  · refine ⟨fun _ => ⟨s, hview _ rfl⟩, fun hcontra => ?_⟩
    exfalso
    simp only [RecRel_strVal, StrRec] at hkr
    exact hcontra hkr.1

/-! ## Twin-side runs of `projLitToCtor` -/

theorem projLitToCtor_run_not_lit (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : Word) (hh : HW h)
    (hg : h >>> 28 ≠ 8) (a : AState) :
    (projLitToCtor r fe depth (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = false := by rw [decE_lit_tag h hh]; simp [hg]
  simp [projLitToCtor, ht, StateT.run_pure]
  rfl

theorem projLitToCtor_run_plain (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (a : AState) (l : ConLeche.Literal)
    (hv : a.store.view (decE h) = some (.lit l)) (hne : ∀ s, l ≠ .strVal s) :
    (projLitToCtor r fe depth (decE h)).run a = .ok (decE h, a) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [projLitToCtor, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind]
  cases l with
  | natVal n => rfl
  | strVal s => exact absurd rfl (hne s)

theorem projLitToCtor_run_unsupported (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : Word)
    (hh : HW h) (hg : h >>> 28 = 8) (a a' : AState) (s : String)
    (hv : a.store.view (decE h) = some (.lit (.strVal s)))
    (hsup : (strLitSupported fe).run a = .ok (false, a')) :
    (projLitToCtor r fe depth (decE h)).run a = .ok (decE h, a') := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [projLitToCtor, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hsup]
  rfl

theorem projLitToCtor_run_ctor (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (h : Word) (hh : HW h)
    (hg : h >>> 28 = 8) (a a' a₁ a₂ : AState) (s : String)
    (hv : a.store.view (decE h) = some (.lit (.strVal s)))
    (hsup : (strLitSupported fe).run a = .ok (true, a')) (c : EIdx)
    (hc : (strLitToConstructor s).run a' = .ok (c, a₁)) (res : EIdx)
    (hres : (r.whnf depth c).run a₁ = .ok (res, a₂)) :
    (projLitToCtor r fe depth (decE h)).run a = .ok (res, a₂) := by
  have ht : ((decE h).tag == ETag.lit) = true := by rw [decE_lit_tag h hh]; simp [hg]
  simp [projLitToCtor, ht, StateT.run_bind, view_run _ _ _ hv, except_ok_bind, hsup, hc, hres]

/-- **`proj_lit_to_ctor` refines `projLitToCtor`.** -/
theorem projLitToCtor_refines' (p : Prog) (hp : WhnfCoreProg p) (hw : WhnfCallees p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb mode d h : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hh : HW h)
    -- `StrLitSupportedOK` (`WhnfBase.lean`) does not say the query keeps the expression store's
    -- nodes; added here, minimally, as the one extra fact this proof needs to carry the `view`
    -- fact across its call (see `SupKeep`).
    (hsupKeep : SupKeep fe) :
    CoreSpec p (n + 1) "proj_lit_to_ctor" [mode, vis, d, h]
      (projLitToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe
      MM eb := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (projLitToCtor_spec p hp n s₀ mode vis d h)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold projLitToCtorW at hW
  by_cases htag : h >>> 28 ≠ 8
  · rw [if_pos htag] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hrun' := projLitToCtor_run_not_lit (coreKnot (decMode mode) fe id F) fe d.toNat h hh htag a₀
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact hh⟩
    rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [if_neg htag] at hW
  have htag8 : h >>> 28 = 8 := by simpa using htag
  by_cases hsc : tierW h ≠ 0 ∧ rdW (s.mem.arr64 CTL) 1 = 0
  · simp [hsc] at hW
  rw [if_neg hsc] at hW
  by_cases hbd : rdW (s.mem.arr64 CTL) (2 + tierW h) ≤ idxW h
  · simp [hbd] at hW
  rw [if_neg hbd] at hW
  have hvOK : viewOK s.mem h 2 := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hviewS, hviewN⟩ := view_lit_kind s.mem a₀ hS.arena.1 h hh hvOK htag8
  by_cases hkind : rdW (s.mem.arr64 REC) (idxW h * 8 + tierW h * 4) ≠ 1
  · rw [if_pos hkind] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    obtain ⟨l, hv, hne⟩ := hviewN hkind
    have hrun' := projLitToCtor_run_plain (coreKnot (decMode mode) fe id F) fe d.toNat h hh htag8 a₀
      l hv hne
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact hh⟩
    rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [if_neg hkind] at hW
  obtain ⟨s', hv⟩ := hviewS (by simpa using hkind)
  cases hcall1 : callW p n "str_lit_supported" [vis] s.mem with
  | none => simp [hcall1] at hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  simp only [hcall1] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, -⟩ :=
    CoreSpec.of_callW (hw.strLitSupported n s a₀ dn vis fe MM eb hS) hcall1
  by_cases hsup0 : r₁.headD 0 = 0
  · rw [if_pos hsup0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hsupF : (strLitSupported fe).run a₀ = .ok (false, AM.st (strLitSupported fe) a₀) := by
      have hrr := AM.run_of_ok _ _ hok1
      rw [hres1] at hrr
      have hdb : decBool r₁ = false := by show (r₁.headD 0 != 0) = false; rw [hsup0]; decide
      rwa [hdb] at hrr
    have hrun' := projLitToCtor_run_unsupported (coreKnot (decMode mode) fe id F) fe d.toNat h hh
      htag8 a₀ _ s' hv hsupF
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact hh⟩
    rw [hst, ← hm]; exact ⟨M₁, hS₁, hK₁, hSt₁⟩
  rw [if_neg hsup0] at hW
  have hsupT : (strLitSupported fe).run a₀ = .ok (true, AM.st (strLitSupported fe) a₀) := by
    have hrr := AM.run_of_ok _ _ hok1
    rw [hres1] at hrr
    have hdb : decBool r₁ = true := by
      show (r₁.headD 0 != 0) = true
      rw [bne_iff_ne]
      exact hsup0
    rwa [hdb] at hrr
  let a₁ : AState := AM.st (strLitSupported fe) a₀
  have hv₁ : a₁.store.view (decE h) = some (.lit (.strVal s')) := by
    show (AM.st (strLitSupported fe) a₀).store.view (decE h) = _
    exact hsupKeep a₀ _ _ hv
  cases hcall2 : callW p n "str_lit_ctor" [h] m₁ with
  | none => simp [hcall2] at hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  simp only [hcall2] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ :=
    CoreSpec.of_callW (hw.strLitCtor n { s with mem := m₁ } a₁ dn vis fe M₁ eb h s' hS₁ hh hv₁)
      hcall2
  cases hcall3 : callW p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with
  | none => rw [hcall3] at hW; simp at hW
  | some q₃ =>
  obtain ⟨r₃, m₃⟩ := q₃
  simp only [hcall3, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  have hslot := (hk n (Nat.le_refl n)).whnf F { s with mem := m₂ }
    (AM.st (strLitToConstructor s') a₁) dn vis fe M₂ eb mode d (r₂.headD 0) hF hn
    ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw2
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := CoreSpec.of_callW hslot hcall3
  have hc2run := AM.run_of_ok _ _ hok2
  rw [hres2] at hc2run
  have hwhnfrun := AM.run_of_ok _ _ hok3
  rw [hres3] at hwhnfrun
  have hrun' := projLitToCtor_run_ctor (coreKnot (decMode mode) fe id F) fe d.toNat h hh htag8 a₀
    a₁ (AM.st (strLitToConstructor s') a₁) _ s' hv hsupT (decH r₂) hc2run _ hwhnfrun
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  refine ⟨hok, ?_, by rw [hres]; exact congrArg decE hr, by unfold ResH; rw [← hr]; exact hrw3⟩
  rw [hst, ← hm]
  exact ⟨M₃, hS₃, hK₁.trans (hK₂.trans hK₃), hSt₁.trans (hSt₂.trans hSt₃)⟩


/-! ## `whnf_core_step_proj` -/

/-- The model of `whnf_core_step_proj`. -/
def stepProjW (p : Prog) (n : Nat) (m : Mem) (mode cheap vis d e sn i pe : Word) :
    Option (Word × Word × Mem) :=
  match (if cheap ≠ 0 then callW p n "whnf_core" [mode, 1, vis, d, pe] m
         else callW p n "whnf" [mode, vis, d, pe] m) with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "reduce_proj_core" [mode, vis, d, sn, i, r₁.headD 0] m₁ with
    | none => none
    | some (r₂, m₂) =>
      if r₂.headD 0 ≠ 0 then some (1, r₂.tail.headD 0, m₂) else some (0, e, m₂)

theorem stepProj_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St)
    (mode cheap vis d e sn i pe : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "whnf_core_step_proj"
      [mode, cheap, vis, d, e, sn, i, pe]
    ⦃fun r s' => LocEq s' s₀ ∧
      stepProjW p n s₀.mem mode cheap vis d e sn i pe = some (r.headD 0, r.tail.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp.sproj]
  simp only [callFn, whnfCoreStepProjL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs,
      callW_spec p n "whnf_core", callW_spec p n "whnf", callW_spec p n "reduce_proj_core"] <;>
  simp_all [stepProjW, Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]


/-! ## `reduce_proj_core` -/

/-- **`reduce_proj_core` refines `reduceProjCore`.** -/
theorem reduceProjCore_refines' (p : Prog) (hp : WhnfCoreProg p) (hw : WhnfCallees p)
    (hc : CoreCallees p) (hl : p.lookup "ls_node" = some lsNode) (hE : ErecKept p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d sn i c : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hsn : HW sn) (hc' : HW c)
    (hsup : SupKeep fe) :
    CoreSpec p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) decOptR s₀ a₀ dn vis fe MM eb ResW := sorry

/-! ## `whnf_core_step_proj` refines -/

/-- The step answer for a projection's reduct. -/
def optStep (e : EIdx) : Option EIdx → WhnfStep
  | some x => .cont x
  | none => .done e

theorem stepProj_run (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (cheap : Bool)
    (depth : Nat) (e : EIdx) (sn : NIdx) (i : Nat) (pe c : EIdx) (a a₁ a₂ : AState)
    (h₁ : (if cheap then r.whnfCore true depth pe else r.whnf depth pe).run a = .ok (c, a₁))
    (m' : Option EIdx) (h₂ : (reduceProjCore mode r fe depth sn i c).run a₁ = .ok (m', a₂)) :
    (whnfCoreStepProj mode r fe cheap depth e sn i pe).run a =
      .ok (optStep e m', a₂) := by
  cases cheap <;> cases m' <;>
    simp_all [whnfCoreStepProj, optStep, StateT.run_bind, except_ok_bind] <;> rfl

/-- **`whnf_core_step_proj` refines `whnfCoreStepProj`.** -/
theorem whnfCoreStepProj_refines' (p : Prog) (hp : WhnfCoreProg p) (hw : WhnfCallees p)
    (hc : CoreCallees p) (hl : p.lookup "ls_node" = some lsNode) (hE : ErecKept p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode cheap d e sn i pe : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e)
    (hsn : HW sn) (hpe : HW pe) (hsup : SupKeep fe) :
    CoreSpec p (n + 1) "whnf_core_step_proj" [mode, cheap, vis, d, e, sn, i, pe]
      (whnfCoreStepProj (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e) (decI sn) i.toNat (decE pe)) decStep s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (stepProj_spec p hp n s₀ mode cheap vis d e sn i pe)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold stepProjW at hW
  -- the scrutinee's normalisation
  have key : ∀ (r₁ : List Word) (m₁ : Mem),
      (if cheap ≠ 0 then callW p n "whnf_core" [mode, 1, vis, d, pe] s.mem
        else callW p n "whnf" [mode, vis, d, pe] s.mem) = some (r₁, m₁) →
      ∃ M₁ a₁, CoreS dn m₁ a₁ vis fe M₁ eb ∧ KeptAll MM M₁ eb ∧ StackKept s.mem m₁ ∧
        HW (r₁.headD 0) ∧
        (if (cheap != 0) = true then (coreKnot (decMode mode) fe id F).whnfCore true d.toNat (decE pe)
          else (coreKnot (decMode mode) fe id F).whnf d.toNat (decE pe)).run a₀ =
          .ok (decE (r₁.headD 0), a₁) := by
    intro r₁ m₁ hcall
    by_cases hch : cheap = 0
    · rw [if_neg (by simpa using hch)] at hcall
      have hslot := (hk n (Nat.le_refl n)).whnf F s a₀ dn vis fe MM eb mode d pe hF hn hs hpe
      obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hslot hcall
      refine ⟨M₁, _, hS₁, hK₁, hSt₁, hrw, ?_⟩
      have := AM.run_of_ok _ _ hok
      rw [hres] at this
      rw [if_neg (by simp [hch])]; exact this
    · rw [if_pos hch] at hcall
      have hslot := (hk n (Nat.le_refl n)).whnfCore F s a₀ dn vis fe MM eb mode 1 d pe hF hn hs hpe
      obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hslot hcall
      refine ⟨M₁, _, hS₁, hK₁, hSt₁, hrw, ?_⟩
      have := AM.run_of_ok _ _ hok
      rw [hres] at this
      rw [if_pos (by simpa using hch)]; exact this
  cases hcall1 : (if cheap ≠ 0 then callW p n "whnf_core" [mode, 1, vis, d, pe] s.mem
      else callW p n "whnf" [mode, vis, d, pe] s.mem) with
  | none => simp [hcall1] at hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  simp only [hcall1] at hW
  obtain ⟨M₁, a₁, hS₁, hK₁, hSt₁, hr₁, hrun₁⟩ := key r₁ m₁ hcall1
  cases hcall2 : callW p n "reduce_proj_core" [mode, vis, d, sn, i, r₁.headD 0] m₁ with
  | none =>
    rw [show r₁.headD 0 = r₁.head?.getD 0 from by cases r₁ <;> rfl] at hcall2
    simp [hcall2] at hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  simp only [hcall2] at hW
  cases n with
  | zero => simp [callW_zero] at hcall2
  | succ N =>
  have hred := reduceProjCore_refines' p hp hw hc hl hE N (hk.mono (by omega)) F (by omega)
    (by omega) { s with mem := m₁ } a₁ dn vis fe M₁ eb mode d sn i (r₁.headD 0)
    ⟨hS₁, hs.mode4, hs.eb_mode⟩ hsn hr₁ hsup
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := CoreSpec.of_callW hred hcall2
  have hrun₂ := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun₂
  have hrun' := stepProj_run (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
    (decE e) (decI sn) i.toNat (decE pe) _ a₀ a₁ _ hrun₁ _ hrun₂
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
  have hW' : (r₂.headD 0 ≠ 0 → r.headD 0 = 1 ∧ r.tail.headD 0 = r₂.tail.headD 0) ∧
      (r₂.headD 0 = 0 → r.headD 0 = 0 ∧ r.tail.headD 0 = e) ∧ m₂ = s'.mem := by
    by_cases hf : r₂.headD 0 = 0
    · rw [if_neg (by simpa using hf)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨h0, h1, hm⟩ := hW
      exact ⟨fun h => absurd hf h, fun _ => ⟨h0.symm, h1.symm⟩, hm⟩
    · rw [if_pos (by simpa using hf)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨h0, h1, hm⟩ := hW
      exact ⟨fun _ => ⟨h0.symm, h1.symm⟩, fun h => absurd h hf, hm⟩
  obtain ⟨hA, hB, hm⟩ := hW'
  subst hm
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst]
    exact ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩
  · rw [hres]
    by_cases hf : r₂.headD 0 = 0
    · obtain ⟨h0, h1⟩ := hB hf
      simp only [decOptR, hf, decOpt_zero, decStep, h0, h1, optStep]; rfl
    · obtain ⟨h0, h1⟩ := hA hf
      simp only [decOptR, decOpt_ne _ _ hf, decStep, h0, h1, optStep]; simp
  · by_cases hf : r₂.headD 0 = 0
    · obtain ⟨h0, h1⟩ := hB hf
      exact ⟨by rw [h0]; unfold HW; decide, by rw [h1]; exact he⟩
    · obtain ⟨h0, h1⟩ := hA hf
      exact ⟨by rw [h0]; unfold HW; decide, by rw [h1]; exact hrw2.2⟩

/-! ## The refinements at the original statements (the stubs instantiated) -/

section wrap
variable (p : Prog) (hp : WhnfCoreProg p)

include hp in
/-- **`whnf_core_step_proj` refines `whnfCoreStepProj`.** -/
@[refines ConRon.Arena.whnfCoreStepProj]
theorem whnfCoreStepProj_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode cheap d e sn i pe : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he : HW e) (hsn : HW sn) (hpe : HW pe) :
    CoreSpec p (n + 1) "whnf_core_step_proj" [mode, cheap, vis, d, e, sn, i, pe]
      (whnfCoreStepProj (decMode mode) (coreKnot (decMode mode) fe id F) fe (cheap != 0) d.toNat
        (decE e) (decI sn) i.toNat (decE pe)) decStep s₀ a₀ dn vis fe MM eb ResW :=
  whnfCoreStepProj_refines' p hp (whnfCallees_stub p) (coreCallees_stub p) hp.lsn
    (coreCallees_stub p).erec n hk F hF hn s₀ a₀ dn vis fe MM eb mode cheap d e sn i pe hs he hsn hpe
    (supKeep_twin fe)

include hp in
/-- **`reduce_proj_core` refines `reduceProjCore`.** -/
@[refines ConRon.Arena.reduceProjCore]
theorem reduceProjCore_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d sn i c : Word)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hsn : HW sn) (hc' : HW c) :
    CoreSpec p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  reduceProjCore_refines' p hp (whnfCallees_stub p) (coreCallees_stub p) hp.lsn
    (coreCallees_stub p).erec n hk F hF hn s₀ a₀ dn vis fe MM eb mode d sn i c hs hsn hc'
    (supKeep_twin fe)

include hp in
/-- **`proj_lit_to_ctor` refines `projLitToCtor`.** -/
@[refines ConRon.Arena.projLitToCtor]
theorem projLitToCtor_refines (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F)
    (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (MM : ModeMaps) (eb mode d h : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) :
    CoreSpec p (n + 1) "proj_lit_to_ctor" [mode, vis, d, h]
      (projLitToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE h)) decH s₀ a₀ dn vis fe
      MM eb :=
  projLitToCtor_refines' p hp (whnfCallees_stub p) n hk F hF hn s₀ a₀ dn vis fe MM eb mode d h hs hh
    (supKeep_twin fe)

end wrap

end L.Arena
