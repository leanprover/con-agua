import ConAgua.Arena.WhnfCoreApp

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


/-! ## The words of a projection table record -/

theorem mapM_option_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length := by
  intro l
  induction l with
  | nil => intro r h; simp [List.mapM_nil] at h; subst h; rfl
  | cons x xs ih =>
    intro r h
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨y, -, ys, hys, rfl⟩ := h
    simp [ih ys hys]

theorem hslice?_length {k : IdxKind} {a : Array Word} {off cnt : Nat} {l : List (Idx k)}
    (h : hslice? a off cnt = some l) : l.length = cnt := by
  have := mapM_option_length _ _ _ h
  simpa using this

theorem add_toNat_of_lt (q : Word) (c : Nat) (hc : c < 2 ^ 63) (h : q.toNat + c < 2 ^ 63) :
    (q + c.toUInt64).toNat = q.toNat + c := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (by omega : c < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]

/-- **The words of a decoded projection table**: the level-parameter count at `q + 4`, the
parameter count at `q + 5`, the constructor handle at `q + 6`, the field count at `q + 7`. -/
theorem decTbl_words {a : Array Word} {q : Word} {tbl : IProjTable}
    (h : decTbl a q.toNat = some tbl) (hsz : a.size < 2 ^ 63) :
    tbl.levelParams.length = (rdW a (q + 4)).toNat ∧ tbl.numParams = (rdW a (q + 5)).toNat ∧
    HW (rdW a (q + 6)) ∧ tbl.ctor = decI (rdW a (q + 6)) ∧
    tbl.numFields = (rdW a (q + 7)).toNat := by
  simp only [decTbl, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at h
  obtain ⟨tn, -, sn, -, lps, hlps, np, hnp, ct, hct, nf, hnf, ss, -, bd, -, gd, -, off, -, hc⟩ := h
  subst hc
  simp only [hlist?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hlps
  obtain ⟨o, ho, c, hcn, hsl⟩ := hlps
  simp only [nat?, Option.map_eq_some_iff] at hnp hnf ho hcn
  obtain ⟨wnp, hwnp, rfl⟩ := hnp
  obtain ⟨wnf, hwnf, rfl⟩ := hnf
  obtain ⟨wc, hwc, rfl⟩ := hcn
  obtain ⟨w6, hw6, hw6l, hw6d⟩ := hd?_eq hct
  have b4 : q.toNat + 3 + 1 < a.size := by
    have := (Array.getElem?_eq_some_iff.mp hwc).1; omega
  have b5 : q.toNat + 5 < a.size := (Array.getElem?_eq_some_iff.mp hwnp).1
  have b6 : q.toNat + 6 < a.size := (Array.getElem?_eq_some_iff.mp hw6).1
  have b7 : q.toNat + 7 < a.size := (Array.getElem?_eq_some_iff.mp hwnf).1
  have e4 := add_toNat_of_lt q 4 (by omega) (by omega)
  have e5 := add_toNat_of_lt q 5 (by omega) (by omega)
  have e6 := add_toNat_of_lt q 6 (by omega) (by omega)
  have e7 := add_toNat_of_lt q 7 (by omega) (by omega)
  have r4 : rdW a (q + 4) = wc := by
    simp only [rdW, show (4 : Word) = (4 : Nat).toUInt64 from rfl, e4,
      show q.toNat + 4 = q.toNat + 3 + 1 from rfl, hwc]; rfl
  have r5 : rdW a (q + 5) = wnp := by
    simp only [rdW, show (5 : Word) = (5 : Nat).toUInt64 from rfl, e5, hwnp]; rfl
  have r6 : rdW a (q + 6) = w6 := by
    simp only [rdW, show (6 : Word) = (6 : Nat).toUInt64 from rfl, e6, hw6]; rfl
  have r7 : rdW a (q + 7) = wnf := by
    simp only [rdW, show (7 : Word) = (7 : Nat).toUInt64 from rfl, e7, hwnf]; rfl
  rw [r4, r5, r6, r7]
  exact ⟨hslice?_length hsl, rfl, hw6l, hw6d, rfl⟩

/-! ## `ls_node` against `viewLsLen` -/

/-- **A level-list handle that `ls_node` reads without aborting has a length in the arena**, and it
is the record's length word. -/
theorem lsNodeW_viewLen {m : Mem} {a : AState} (hR : ArenaR m a) {h : Word} (hh : h.toNat < 2 ^ 32)
    {o l : Word} (hl : lsNodeW m h = [o, l]) : a.store.lss.viewLen (decI h) = some l.toNat := by
  have hfl := hR.ls.2.1
  have ht1 := tierW_le h
  have hpers : (decI h : LsIdx).isPersistent = (tierW h == 0) := by
    rw [isPersistent_decI h hh]; rfl
  unfold lsNodeW at hl
  by_cases g0 : h >>> 28 ≠ 0
  · simp [g0] at hl
  rw [if_neg g0] at hl
  by_cases hsc : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hsc] at hl
  rw [if_neg hsc] at hl
  by_cases hbd : rdW (m.arr64 CTL) (40 + tierW h) ≤ idxW h
  · simp [hbd] at hl
  rw [if_neg hbd] at hl
  have g0' : h >>> 28 = 0 := by simpa using g0
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨rfl, rfl⟩ := hl
  have htag := decLs_tag0 h hh
  simp only [g0', beq_self_eq_true] at htag
  unfold LsStore.viewLen
  rw [hpers]
  rcases word_le_one (tierW h) ht1 with h0 | h1
  · -- persistent
    have hT := hR.ls.2.2.1
    have hlt : (idxW h).toNat < a.store.lss.pers.lists.nodes.size := by
      rw [← hT.1]
      have : ¬ rdW (m.arr64 CTL) (40 + 0) ≤ idxW h := by rw [h0] at hbd; exact hbd
      exact UInt64.not_le.mp this
    obtain ⟨x, hx⟩ : ∃ x, a.store.lss.pers.lists.nodes[(idxW h).toNat]? = some x :=
      ⟨_, Array.getElem?_eq_getElem hlt⟩
    obtain ⟨-, hr⟩ := tier_node lsSch LsRecRel lshash m _ _ _ hR.ls (tierW h) ht1 (idxW h) x
      (by rw [h0]; simpa using hx)
    simp only [LsRecRel] at hr
    have hlen := congrArg List.length hr.2.1
    rw [sliceL_length] at hlen
    simp only [lsWords, List.length_map] at hlen
    simp only [h0, beq_self_eq_true, ↓reduceIte, LsStore.persGetLen, LsTables.getLen, htag,
      Tbl.node?, decLs_idx h, hx, Option.map_some]
    simp only [lsL, h0] at hlen
    rw [hlen]
  · have hsc' : rdW (m.arr64 CTL) 1 ≠ 0 := fun e => hsc ⟨by rw [h1]; decide, e⟩
    have hon : a.store.lss.scratchOn = true := by
      rw [← hfl]; simpa using hsc'
    have hT := hR.ls.2.2.2
    have hlt : (idxW h).toNat < a.store.lss.scr.lists.nodes.size := by
      rw [← hT.1]
      have : ¬ rdW (m.arr64 CTL) (40 + 1) ≤ idxW h := by rw [h1] at hbd; exact hbd
      exact UInt64.not_le.mp this
    obtain ⟨x, hx⟩ : ∃ x, a.store.lss.scr.lists.nodes[(idxW h).toNat]? = some x :=
      ⟨_, Array.getElem?_eq_getElem hlt⟩
    obtain ⟨-, hr⟩ := tier_node lsSch LsRecRel lshash m _ _ _ hR.ls (tierW h) ht1 (idxW h) x
      (by rw [h1]; simpa using hx)
    simp only [LsRecRel] at hr
    have hlen := congrArg List.length hr.2.1
    rw [sliceL_length] at hlen
    simp only [lsWords, List.length_map] at hlen
    simp only [h1, ↓reduceIte, hon, LsTables.getLen, htag, Tbl.node?, decLs_idx h, hx,
      Option.map_some]
    simp only [lsL, h1] at hlen
    rw [hlen]; simp

/-! ## `intern_bvar` as a run -/

theorem keeps_cpl_internBVar (i : Nat) : Keeps cpl (internE (.bvar i)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- An interned `bvar` handle word is below `2^32`. -/
theorem binternW_hw (m : Mem) (a : AState) (hR : BVarR m a) (u w : Word) (m' : Mem)
    (hI : binternW m u = some (w, m')) : w.toNat < 2 ^ 32 := by
  rw [binternW_eq] at hI
  exact internM_hw bvarSch BRecRel bhash bvarSch_wf m _ _ _ hR (bMt m u) _ _ _ _
    (probe_homeG bvarSch m 0 _ _ (bprobeW_arm m u 0) _)
    (probe_homeG bvarSch m 1 _ _ (bprobeW_arm m u 1) _) _ (bpushOK_room m) _ _ w m' hI

theorem binternW_frame (m : Mem) (u w : Word) (m' : Mem) (hI : binternW m u = some (w, m')) :
    MemFrame [BREC, BSLOT] [22, 23] m m' := by
  rw [binternW_eq] at hI
  exact internM_frame bvarSch bvarSch_wf _ _ _ _ _ _ _ _ hI

/-- **`intern_bvar` as a run.** -/
theorem callW_internBVar (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (u : Word) (r : List Word) (m' : Mem)
    (h : callW p n "intern_bvar" [u] s₀.mem = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a₀ ∧
    ArenaD m' (AM.st (internE (.bvar u.toNat)) a₀) ∧
    AM.res (internE (.bvar u.toNat)) a₀ = decE (r.headD 0) ∧
    MemFrame [BREC, BSLOT] [22, 23] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (internBVar_spec p hp.bvf hp.bvp hp.bvi n s₀ u) h
  obtain ⟨h1, h2, h3⟩ := internBVar_D s₀.mem a₀ hD u _ _ hm
  exact ⟨h1, h2, h3, binternW_frame _ _ _ _ hm, binternW_hw _ a₀ hD.1.bvar _ _ _ hm⟩

/-- **`CoreS` across a `bvar` interning step.** -/
theorem CoreS.of_bvar {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame [BREC, BSLOT] [22, 23] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl <;> decide)
    (by simp [BREC, BSLOT])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)

theorem StackKept.of_bvar_frame {m m' : Mem} (hf : MemFrame [BREC, BSLOT] [22, 23] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [BREC, BSLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact ⟨by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩

/-- A slice survives a change that leaves the stack array alone. -/
theorem SpineR.of_spn {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (hs : m'.arr64 SPN = m.arr64 SPN) : SpineR m' off cnt xs := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, by rw [hs]; exact h2, fun i hi => ?_, fun i hi => ?_⟩
  · simp only [spW, hs] at h3 ⊢; exact h3 i hi
  · simp only [spW, hs] at h4 ⊢; exact h4 i hi

/-! ## `reduce_proj_arg` -/

/-- The twin's fire: the argument (else `bvar 0`), certified at the verified mode. -/
def rpArgT (fe : IFEnv) (verified : Bool) (k : NIdx) (args : List EIdx) (j : Nat) :
    AM (Option EIdx) := do
  let b0 ← internE (.bvar 0)
  let arg := args.getD j b0
  if ← projCertAt fe verified k args then pure (some arg) else pure none

/-- The model of `reduce_proj_arg`. -/
def rpArgW (p : Prog) (n : Nat) (m : Mem) (mode vis k ao an j : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "intern_bvar" [0] m with
  | none => none
  | some (r₁, m₁) =>
    if mode &&& 1 = 0 then
      match callW p n "proj_cert" [vis, k, ao, an] m₁ with
      | none => none
      | some (r₂, m₂) =>
        if r₂.headD 0 ≠ 0 then
          some (1, (if j < an then rdW (m₁.arr64 SPN) (ao + j) else r₁.headD 0), m₂)
        else some (0, 0, m₂)
    else some (1, (if j < an then rdW (m₁.arr64 SPN) (ao + j) else r₁.headD 0), m₁)

theorem rpArg_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St)
    (mode vis k ao an j : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_proj_arg" [mode, vis, k, ao, an, j]
    ⦃fun r s' => LocEq s' s₀ ∧
      rpArgW p n s₀.mem mode vis k ao an j = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.rparg]
  simp only [callFn, reduceProjArgL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "intern_bvar", callW_spec p n "proj_cert"] <;>
    finish [rpArgW]

theorem mode_cases (mode : Word) (h : mode < 4) : mode = 0 ∨ mode = 1 ∨ mode = 2 ∨ mode = 3 := by
  have h' : mode.toNat < 4 := UInt64.lt_iff_toNat_lt.mp h
  have : mode.toNat = 0 ∨ mode.toNat = 1 ∨ mode.toNat = 2 ∨ mode.toNat = 3 := by omega
  rcases this with e | e | e | e
  · left; exact UInt64.toNat_inj.mp e
  · right; left; exact UInt64.toNat_inj.mp e
  · right; right; left; exact UInt64.toNat_inj.mp e
  · right; right; right; exact UInt64.toNat_inj.mp e

/-- The mode test of `reduce_proj_arg` is `verifiedChecks`. -/
theorem decMode_verified (mode : Word) (h : mode < 4) :
    (decMode mode).verifiedChecks = decide (mode &&& 1 = 0) := by
  rcases mode_cases mode h with rfl | rfl | rfl | rfl <;> decide

theorem rpArg_refines (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode k ao an j : Word) (args : Array EIdx) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hk : HW k) (har : SpineR s₀.mem ao an args) :
    CoreSpec p (n + 1) "reduce_proj_arg" [mode, vis, k, ao, an, j]
      (rpArgT fe (decMode mode).verifiedChecks (decI k) args.toList j.toNat) decOptR s₀ a₀ dn vis fe
      MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (rpArg_spec p hp n s₀ mode vis k ao an j)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold rpArgW at hW
  cases hc1 : callW p n "intern_bvar" [0] s.mem with
  | none => simp [hc1] at hW
  | some q₁ =>
  obtain ⟨r₁, m₁⟩ := q₁
  simp only [hc1] at hW
  obtain ⟨hok1, hD1, hres1, hfr1, hhw1⟩ := callW_internBVar p hp n s a₀ hS.arena 0 r₁ m₁ hc1
  have h0 : (0 : Word).toNat = 0 := rfl
  rw [h0] at hok1 hD1 hres1
  obtain ⟨a₁, ha₁⟩ : ∃ a₁, a₁ = AM.st (internE (.bvar 0)) a₀ := ⟨_, rfl⟩
  rw [← ha₁] at hD1
  have hcpl : cpl a₁ = cpl a₀ := by
    have := AM.run_of_ok _ _ hok1
    exact Keeps.run (keeps_cpl_internBVar 0) (by rw [ha₁]; exact this)
  have hS₁ : CoreS dn m₁ a₁ vis fe MM eb := hS.of_bvar hD1 hcpl hfr1
  have hX : (internE (.bvar 0)).run a₀ = .ok (decE (r₁.headD 0), a₁) := by
    have := AM.run_of_ok _ _ hok1
    rw [hres1, ← ha₁] at this; exact this
  have hspn : m₁.arr64 SPN = s.mem.arr64 SPN := hfr1.1 SPN (by simp [BREC, BSLOT, SPN]) (by decide)
  have har₁ : SpineR m₁ ao an args := har.of_spn hspn
  have hSt₁ : StackKept s.mem m₁ := StackKept.of_bvar_frame hfr1
  have hMD := decMode_verified mode hs.mode4
  -- the argument word and its decoding
  have harg : ∀ w : Word, (w = if j < an then rdW (m₁.arr64 SPN) (ao + j) else r₁.headD 0) →
      HW w ∧ args.toList.getD j.toNat (decE (r₁.headD 0)) = decE w := by
    intro w hw
    by_cases hj : j < an
    · rw [if_pos hj] at hw
      have hj' : j.toNat < an.toNat := hj
      have hjs : j.toNat < args.size := by rw [har₁.size]; exact hj'
      have hat : (ao + j) = ao + j.toNat.toUInt64 := by simp
      refine ⟨hw ▸ ?_, ?_⟩
      · rw [hat]; exact har₁.lt j.toNat hj'
      · rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_pos (by simpa using hjs)]
        simp only [Array.getElem_toList]
        rw [har₁.get j.toNat hjs, hw, hat]; rfl
    · rw [if_neg hj] at hw
      have hj' : ¬ j.toNat < an.toNat := hj
      refine ⟨hw ▸ hhw1, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dif_neg (by simp [har₁.size]; omega), hw]
  by_cases hv : mode &&& 1 = 0
  · rw [if_pos hv] at hW
    cases hc2 : callW p n "proj_cert" [vis, k, ao, an] m₁ with
    | none => simp [hc2] at hW
    | some q₂ =>
    obtain ⟨r₂, m₂⟩ := q₂
    simp only [hc2] at hW
    cases n with
    | zero => simp [callW_zero] at hc2
    | succ N =>
    have hcert := projCert_refines p hp N { s with mem := m₁ } a₁ dn vis fe MM eb k ao an args
      hS₁ hk har₁
    obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, -⟩ := CoreSpec.of_callW hcert hc2
    have hY := AM.run_of_ok _ _ hok2
    rw [hres2] at hY
    have hver : (decMode mode).verifiedChecks = true := by rw [hMD]; simpa using hv
    by_cases hf : r₂.headD 0 ≠ 0
    · rw [if_pos hf] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      obtain ⟨hwh, hwd⟩ := harg _ rfl
      have hT : (rpArgT fe (decMode mode).verifiedChecks (decI k) args.toList j.toNat).run a₀ =
          .ok (some (decE (r.tail.headD 0)), AM.st (projCert fe (decI k) args.toList) a₁) := by
        have hdb : decBool r₂ = true := by simpa [decBool] using hf
        rw [hdb] at hY
        simp only [rpArgT, projCertAt, hver, if_true, StateT.run_bind, hX, except_ok_bind, hY]
        rw [← hr1, hwd]; rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
      refine ⟨hok, ?_, ?_, ?_⟩
      · rw [hst, ← hm]; exact ⟨M₂, hS₂, hK₂, hSt₁.trans hSt₂⟩
      · rw [hres]; unfold decOptR; rw [← hr0, decOpt_ne _ _ (by decide)]
      · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hwh⟩
    · rw [if_neg hf] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      have hT : (rpArgT fe (decMode mode).verifiedChecks (decI k) args.toList j.toNat).run a₀ =
          .ok (none, AM.st (projCert fe (decI k) args.toList) a₁) := by
        have hdb : decBool r₂ = false := by simpa [decBool] using hf
        rw [hdb] at hY
        simp only [rpArgT, projCertAt, hver, if_true, StateT.run_bind, hX, except_ok_bind, hY]
        rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
      refine ⟨hok, ?_, ?_, ?_⟩
      · rw [hst, ← hm]; exact ⟨M₂, hS₂, hK₂, hSt₁.trans hSt₂⟩
      · rw [hres]; unfold decOptR; rw [← hr0]; rfl
      · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, by unfold HW; decide⟩
  · rw [if_neg hv] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    obtain ⟨hwh, hwd⟩ := harg _ rfl
    have hver : (decMode mode).verifiedChecks = false := by rw [hMD]; simpa using hv
    have hT : (rpArgT fe (decMode mode).verifiedChecks (decI k) args.toList j.toNat).run a₀ =
        .ok (some (decE (r.tail.headD 0)), a₁) := by
      simp only [rpArgT, projCertAt, hver, StateT.run_bind, hX, except_ok_bind]
      rw [← hr1, hwd]; rfl
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact ⟨MM, hS₁, KeptAll.refl _ _, hSt₁⟩
    · rw [hres]; unfold decOptR; rw [← hr0, decOpt_ne _ _ (by decide)]
    · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hwh⟩

/-! ## `reduce_proj_fire` -/

/-- The twin at a constant head `k.{us}`: the arguments, the level count, the entry's fire check,
the shape conditions, the fire. -/
def rpFireT (mode : ConLeche.CheckMode) (fe : IFEnv) (entry : IProjEntry) (i : Nat) (e' : EIdx)
    (k : NIdx) (us : LsIdx) : AM (Option EIdx) := do
  let args ← getAppArgs coreWalkFuel e'
  match ← viewLsLen us with
  | none => failDanglingLs
  | some usl =>
    let fok ← entry.fireOk us
    if k = entry.ctor ∧ i < entry.numFields ∧ args.length = entry.numParams + entry.numFields ∧
        usl = entry.levelParams.length ∧ fok = true then
      rpArgT fe mode.verifiedChecks k args (entry.numParams + i)
    else pure none

/-- The model of `reduce_proj_fire`. -/
def rpFireW (p : Prog) (n : Nat) (m : Mem) (mode vis e1 q i k us : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "get_app_args" [e1] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "ls_node" [us] m₁ with
    | none => none
    | some (r₂, m₂) =>
      match callW p n "fire_ok" [q, i, us] m₂ with
      | none => none
      | some (r₃, m₃) =>
        if k = rdW (m₃.arr64 EREC) (q + 6) ∧ i < rdW (m₃.arr64 EREC) (q + 7) ∧
            r₁.tail.headD 0 = rdW (m₃.arr64 EREC) (q + 5) + rdW (m₃.arr64 EREC) (q + 7) ∧
            r₂.tail.headD 0 = rdW (m₃.arr64 EREC) (q + 4) ∧ r₃.headD 0 ≠ 0 then
          match callW p n "reduce_proj_arg" [mode, vis, k, r₁.headD 0, r₁.tail.headD 0,
              rdW (m₃.arr64 EREC) (q + 5) + i] m₃ with
          | none => none
          | some (r₄, m₄) => some (r₄.headD 0, r₄.tail.headD 0, m₄)
        else some (0, 0, m₃)

theorem getElem_rdW' (a : Array Word) (x : Word) (h : x.toNat < a.size) : a[x.toNat] = rdW a x := by
  simp [rdW, h]

theorem rpFire_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St)
    (mode vis e1 q i k us : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_proj_fire" [mode, vis, e1, q, i, k, us]
    ⦃fun r s' => LocEq s' s₀ ∧
      rpFireW p n s₀.mem mode vis e1 q i k us = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.rpfire]
  simp only [callFn, reduceProjFireL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "get_app_args", callW_spec p n "ls_node", callW_spec p n "fire_ok",
      callW_spec p n "reduce_proj_arg"] <;>
  simp_all [-UInt64.toNat_add, rpFireW, EREC, BinOp.eval, getElem_rdW', Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr] <;>
  (intro h1; exact absurd h1 (UInt64.not_lt.mpr ‹_›))

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
