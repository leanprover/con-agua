import ConAgua.Arena.ProjView
import ConAgua.Arena.WhnfCoreApp
import ConAgua.Arena.WhnfCoreSlot
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

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
  else if tcnt m LIT (tierW h) ≤ idxW h then none
  else if tfld m LIT (tierW h) (idxW h) 0 ≠ 1 then some (h, m)
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
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
    (hv : viewOK m h LIT) (hg : h >>> 28 = 8) :
    (tfld m LIT (tierW h) (idxW h) 0 = 1 →
      ∃ s, a.store.view (decE h) = some (.lit (.strVal s))) ∧
    (tfld m LIT (tierW h) (idxW h) 0 ≠ 1 →
      ∃ l, a.store.view (decE h) = some (.lit l) ∧ ∀ s, l ≠ .strVal s) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h litCS RecRel (·.lits) _ hR.lit.2 hv.2
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
theorem projLitToCtor_refines' (p : Prog) (hp : WhnfCoreProg p) (hStrSup : StrLitSupportedOK p)
    (hStrCtor : StrLitCtorOK p) (n : Nat)
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
  · rw [ite_eq_left htag] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    have hrun' := projLitToCtor_run_not_lit (coreKnot (decMode mode) fe id F) fe d.toNat h hh htag a₀
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact hh⟩
    rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [ite_eq_right htag] at hW
  have htag8 : h >>> 28 = 8 := by simpa using htag
  obtain ⟨hsc, hW⟩ := of_ite_none hW
  obtain ⟨hbd, hW⟩ := of_ite_none hW
  have hvOK : viewOK s.mem h LIT := ⟨hsc, by simpa using hbd⟩
  obtain ⟨hviewS, hviewN⟩ := view_lit_kind s.mem a₀ hS.arena.1 h hh hvOK htag8
  by_cases hkind : tfld s.mem LIT (tierW h) (idxW h) 0 ≠ 1
  · rw [ite_eq_left hkind] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨l, hv, hne⟩ := hviewN hkind
    have hrun' := projLitToCtor_run_plain (coreKnot (decMode mode) fe id F) fe d.toNat h hh htag8 a₀
      l hv hne
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun'
    refine ⟨hok, ?_, by rw [hres, decH, ← hr], by unfold ResH; rw [← hr]; exact hh⟩
    rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, StackKept.refl _⟩
  rw [ite_eq_right hkind] at hW
  obtain ⟨s', hv⟩ := hviewS (by simpa using hkind)
  rcases hcall1 : callW p n "str_lit_supported" [vis] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [hcall1, reduceCtorEq] at hW
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, -⟩ :=
    CoreSpec.of_callW (hStrSup n s a₀ dn vis fe MM eb hS) hcall1
  by_cases hsup0 : r₁.headD 0 = 0
  · rw [ite_eq_left hsup0] at hW
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj hW)
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
  rw [ite_eq_right hsup0] at hW
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
  rcases hcall2 : callW p n "str_lit_ctor" [h] m₁ with _ | ⟨r₂, m₂⟩
    <;> simp only [hcall2, reduceCtorEq] at hW
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ :=
    CoreSpec.of_callW (hStrCtor n { s with mem := m₁ } a₁ dn vis fe M₁ eb h s' hS₁ hh hv₁)
      hcall2
  rcases hcall3 : callW p n "whnf" [mode, vis, d, r₂.headD 0] m₂ with _ | ⟨r₃, m₃⟩
    <;> simp only [hcall3, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hW
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
  obtain ⟨sn, -, lps, hlps, np, hnp, ct, hct, nf, hnf, ss, -, bd, -, gd, -, hc⟩ := h
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
  have hfl := ConsR.flag hR.ls
  have ht1 := tierW_le h
  have hpers : (decI h : LsIdx).isPersistent = (tierW h == 0) := by
    rw [isPersistent_decI h hh]; rfl
  unfold lsNodeW at hl
  by_cases g0 : h >>> 28 ≠ 0
  · simp [g0] at hl
  rw [ite_eq_right g0] at hl
  by_cases hsc : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · simp [hsc] at hl
  rw [ite_eq_right hsc] at hl
  by_cases hbd : tcnt m LVLS (tierW h) ≤ idxW h
  · simp [hbd] at hl
  rw [ite_eq_right hbd] at hl
  have g0' : h >>> 28 = 0 := by simpa using g0
  simp only [List.cons.injEq, and_true] at hl
  obtain ⟨rfl, rfl⟩ := hl
  have htag := decLs_tag0 h hh
  simp only [g0', beq_self_eq_true] at htag
  unfold LsStore.viewLen
  rw [hpers]
  rcases word_le_one (tierW h) ht1 with h0 | h1
  · -- persistent
    have hlt : (idxW h).toNat < a.store.lss.pers.lists.nodes.size := by
      rw [← ConsR.cntP hR.ls]
      have : ¬ tcnt m LVLS 0 ≤ idxW h := by rw [h0] at hbd; exact hbd
      exact UInt64.not_le.mp this
    obtain ⟨x, hx⟩ : ∃ x, a.store.lss.pers.lists.nodes[(idxW h).toNat]? = some x :=
      ⟨_, Array.getElem?_eq_getElem hlt⟩
    obtain ⟨-, hr⟩ := tier_node lsCS LsRecRel m _ _ _ hR.ls (tierW h) ht1 (idxW h) x
      (by rw [h0]; simpa using hx)
    simp only [LsRecRel] at hr
    have hlen := congrArg List.length hr.2.1
    rw [sliceL_length] at hlen
    simp only [lsWords, List.length_map] at hlen
    simp only [h0, beq_self_eq_true, ↓reduceIte, LsStore.persGetLen, LsTables.getLen, htag,
      Tbl.node?, decLs_idx h, hx, Option.map_some]
    simp only [h0] at hlen
    rw [hlen]
  · have hsc' : rdW (m.arr64 CTL) 1 ≠ 0 := fun e => hsc ⟨by rw [h1]; decide, e⟩
    have hon : a.store.lss.scratchOn = true := by
      rw [← hfl]; simpa using hsc'
    have hlt : (idxW h).toNat < a.store.lss.scr.lists.nodes.size := by
      rw [← ConsR.cntS hR.ls]
      have : ¬ tcnt m LVLS 1 ≤ idxW h := by rw [h1] at hbd; exact hbd
      exact UInt64.not_le.mp this
    obtain ⟨x, hx⟩ : ∃ x, a.store.lss.scr.lists.nodes[(idxW h).toNat]? = some x :=
      ⟨_, Array.getElem?_eq_getElem hlt⟩
    obtain ⟨-, hr⟩ := tier_node lsCS LsRecRel m _ _ _ hR.ls (tierW h) ht1 (idxW h) x
      (by rw [h1]; simpa using hx)
    simp only [LsRecRel] at hr
    have hlen := congrArg List.length hr.2.1
    rw [sliceL_length] at hlen
    simp only [lsWords, List.length_map] at hlen
    simp only [h1, ↓reduceIte, hon, LsTables.getLen, htag, Tbl.node?, decLs_idx h, hx,
      Option.map_some]
    simp only [h1] at hlen
    rw [hlen]; simp

/-! ## `intern_bvar` as a run -/

theorem keeps_cpl_internBVar (i : Nat) : Keeps cpl (internE (.bvar i)) := by
  simp only [internE]; exact keeps_cpl_internNodeE _

/-- An interned `bvar` handle word is below `2^32`. -/
theorem binternW_hw (m : Mem) (a : AState) (hR : BVarR m a) (u w : Word) (m' : Mem)
    (hI : binternW m u = some (w, m')) : w.toNat < 2 ^ 32 := by
  exact consInternM_lt bvarCS_wf hR hI

theorem binternW_frame (m : Mem) (u w : Word) (m' : Mem) (hI : binternW m u = some (w, m')) :
    MemFrame [BREC, BSLOT, BREC + 256, BSLOT + 256] [22, 23] m m' := by
  exact (consInternM_frame bvarCS_wf hI).mono (by simp [ConsSch.wset, bvarCS])
    (by simp [bvarCS])

/-- **`intern_bvar` as a run.** -/
theorem callW_internBVar (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hD : ArenaD s₀.mem a₀) (u : Word) (r : List Word) (m' : Mem)
    (h : callW p n "intern_bvar" [u] s₀.mem = some (r, m')) :
    AM.ok (internE (.bvar u.toNat)) a₀ ∧
    ArenaD m' (AM.st (internE (.bvar u.toNat)) a₀) ∧
    AM.res (internE (.bvar u.toNat)) a₀ = decE (r.headD 0) ∧
    MemFrame [BREC, BSLOT, BREC + 256, BSLOT + 256] [22, 23] s₀.mem m' ∧ HW (r.headD 0) := by
  obtain ⟨s', rfl, -, hm⟩ := triple_of_callW (internBVar_spec p hp.bvf hp.bvp hp.bvi n s₀ u) h
  obtain ⟨h1, h2, h3⟩ := internBVar_D s₀.mem a₀ hD u _ _ hm
  exact ⟨h1, h2, h3, binternW_frame _ _ _ _ hm, binternW_hw _ a₀ hD.1.bvar _ _ _ hm⟩

/-- **`CoreS` across a `bvar` interning step.** -/
theorem CoreS.of_bvar {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (hD : ArenaD m' a')
    (hcpl : cpl a' = cpl a) (hf : MemFrame [BREC, BSLOT, BREC + 256, BSLOT + 256] [22, 23] m m') :
    CoreS dn m' a' vis fe M eb :=
  hS.arena_frame hD hcpl hf
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> decide)
    (by simp [BREC, BSLOT])
    (fun b hb => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)
    (fun x hx => by
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
      rcases hx with rfl | rfl <;> decide)

theorem StackKept.of_bvar_frame {m m' : Mem} (hf : MemFrame [BREC, BSLOT, BREC + 256, BSLOT + 256] [22, 23] m m') :
    StackKept m m' := by
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (by simp [BREC, BSLOT, SPN]) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 := hf.2.1 136 (by simp)
  exact StackKept.of_frame hf

/-- A slice survives a change that leaves the stack array alone. -/
theorem SpineR.of_spn_core {m m' : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
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
  rcases hc1 : callW p n "intern_bvar" [0] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [hc1, reduceCtorEq] at hW
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
  have har₁ : SpineR m₁ ao an args := har.of_spn_core hspn
  have hSt₁ : StackKept s.mem m₁ := StackKept.of_bvar_frame hfr1
  have hMD := decMode_verified mode hs.mode4
  -- the argument word and its decoding
  have harg : ∀ w : Word, (w = if j < an then rdW (m₁.arr64 SPN) (ao + j) else r₁.headD 0) →
      HW w ∧ args.toList.getD j.toNat (decE (r₁.headD 0)) = decE w := by
    intro w hw
    by_cases hj : j < an
    · rw [ite_eq_left hj] at hw
      have hj' : j.toNat < an.toNat := hj
      have hjs : j.toNat < args.size := by rw [har₁.size]; exact hj'
      have hat : (ao + j) = ao + j.toNat.toUInt64 := by simp
      refine ⟨hw ▸ ?_, ?_⟩
      · rw [hat]; exact har₁.lt j.toNat hj'
      · rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dite_eq_left (by simpa using hjs)]
        simp only [Array.getElem_toList]
        rw [har₁.get j.toNat hjs, hw, hat]; rfl
    · rw [ite_eq_right hj] at hw
      have hj' : ¬ j.toNat < an.toNat := hj
      refine ⟨hw ▸ hhw1, ?_⟩
      rw [List.getD_eq_getElem?_getD, List.getD_getElem?, dite_eq_right (by simp [har₁.size]; omega), hw]
  by_cases hv : mode &&& 1 = 0
  · rw [ite_eq_left hv] at hW
    rcases hc2 : callW p n "proj_cert" [vis, k, ao, an] m₁ with _ | ⟨r₂, m₂⟩
      <;> simp only [hc2, reduceCtorEq] at hW
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
    · rw [ite_eq_left hf] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      obtain ⟨hwh, hwd⟩ := harg _ rfl
      have hT : (rpArgT fe (decMode mode).verifiedChecks (decI k) args.toList j.toNat).run a₀ =
          .ok (some (decE (r.tail.headD 0)), AM.st (projCert fe (decI k) args.toList) a₁) := by
        have hdb : decBool r₂ = true := by simpa [decBool] using hf
        rw [hdb] at hY
        simp only [rpArgT, projCertAt, hver, ite_true, StateT.run_bind, hX, except_ok_bind, hY]
        rw [← hr1, hwd]; rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
      refine ⟨hok, ?_, ?_, ?_⟩
      · rw [hst, ← hm]; exact ⟨M₂, hS₂, hK₂, hSt₁.trans hSt₂⟩
      · rw [hres]; unfold decOptR; rw [← hr0, decOpt_ne _ _ (by decide)]
      · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, hwh⟩
    · rw [ite_eq_right hf] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hr0, hr1, hm⟩ := hW
      have hT : (rpArgT fe (decMode mode).verifiedChecks (decI k) args.toList j.toNat).run a₀ =
          .ok (none, AM.st (projCert fe (decI k) args.toList) a₁) := by
        have hdb : decBool r₂ = false := by simpa [decBool] using hf
        rw [hdb] at hY
        simp only [rpArgT, projCertAt, hver, ite_true, StateT.run_bind, hX, except_ok_bind, hY]
        rfl
      obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
      refine ⟨hok, ?_, ?_, ?_⟩
      · rw [hst, ← hm]; exact ⟨M₂, hS₂, hK₂, hSt₁.trans hSt₂⟩
      · rw [hres]; unfold decOptR; rw [← hr0]; rfl
      · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, by unfold HW; decide⟩
  · rw [ite_eq_right hv] at hW
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

/-- `getAppArgs_refines` (`WhnfSpine.lean`) behind one adapter. -/
theorem getAppArgs_spec' (p : Prog) (_hp : SpineProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (hR : ArenaR s₀.mem a₀) (e : Word) (he : HW e) (hspn : (s₀.mem.arr64 SPN).size < 2 ^ 63) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "get_app_args" [e]
    ⦃fun r s' => LocEq s' s₀ ∧ MemFrame [SPN] [136] s₀.mem s'.mem ∧ StackGrew s₀.mem s'.mem ∧
      r.headD 0 = spTop s₀.mem ∧ spTop s'.mem = spTop s₀.mem + r.tail.headD 0 ∧
      ∃ xs, (getAppArgs coreWalkFuel (decE e)).run a₀ = .ok (xs, a₀) ∧
        SpineR s'.mem (r.headD 0) (r.tail.headD 0) xs.toArray; ⊤⦄ :=
  getAppArgs_refines p _hp n s₀ a₀ hR e he hspn

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
            rdW (m₃.arr64 EREC) (q + 7) ≤ r₁.tail.headD 0 ∧
            r₁.tail.headD 0 - rdW (m₃.arr64 EREC) (q + 7) = rdW (m₃.arr64 EREC) (q + 5) ∧
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
  (intro h1; first | exact absurd h1 (UInt64.not_lt.mpr ‹_›) | exact absurd h1 (UInt64.not_le.mpr ‹_›))

/-! ## Runs that leave their pushed slice on the stack -/

/-- **After a core run that left a slice on the stack**: as `CoreAfter`, the stack below the old top
kept, the top possibly grown. -/
def CoreAfterG (dn : NIdx → Option ConLeche.Name) (m₀ m : Mem) (a : AState) (vis : Word)
    (fe : IFEnv) (M : ModeMaps) (eb : Word) : Prop :=
  ∃ M', CoreS dn m a vis fe M' eb ∧ KeptAll M M' eb ∧ StackGrew m₀ m

theorem CoreAfter.toG {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (h : CoreAfter dn m₀ m a vis fe M eb) :
    CoreAfterG dn m₀ m a vis fe M eb :=
  let ⟨M', hS, hK, hSt⟩ := h
  ⟨M', hS, hK, hSt.toGrew⟩

/-- `CoreRef` with `CoreAfterG`. -/
def GrowRef {α : Type} [Inhabited α] (T : AM α) (a₀ : AState) (dec : List Word → α)
    (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb : Word) (r : List Word) (m : Mem) (ok : List Word → Prop := ResH) : Prop :=
  AM.ok T a₀ ∧ CoreAfterG dn m₀ m (AM.st T a₀) vis fe M eb ∧ AM.res T a₀ = dec r ∧ ok r

/-- `CoreSpec` with `GrowRef`. -/
def GrowSpec {α : Type} [Inhabited α] (p : Prog) (n : Nat) (f : FnName) (args : List Word)
    (T : AM α) (dec : List Word → α) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name)
    (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word) (ok : List Word → Prop := ResH) : Prop :=
  ⦃fun s => s = s₀⦄
  invoke p (exec p n) f args
  ⦃fun r s' => LocEq s' s₀ ∧ GrowRef T a₀ dec dn s₀.mem vis fe M eb r s'.mem ok; ⊤⦄

theorem GrowSpec.of_callW {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop}
    (h : GrowSpec p n f args T dec s₀ a₀ dn vis fe M eb ok) {r : List Word} {m' : Mem}
    (hc : callW p n f args s₀.mem = some (r, m')) :
    GrowRef T a₀ dec dn s₀.mem vis fe M eb r m' ok := by
  obtain ⟨t, rfl, -, hr⟩ := triple_of_callW h hc
  exact hr

/-- A `CoreSpec` is a `GrowSpec`. -/
theorem GrowSpec.of_core {α : Type} [Inhabited α] {p : Prog} {n : Nat} {f : FnName}
    {args : List Word} {T : AM α} {dec : List Word → α} {s₀ : St} {a₀ : AState}
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}
    {ok : List Word → Prop} (h : CoreSpec p n f args T dec s₀ a₀ dn vis fe M eb ok) :
    GrowSpec p n f args T dec s₀ a₀ dn vis fe M eb ok := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hok, hA, hres, hr⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun h
  exact ⟨hloc, hok, hA.toG, hres, hr⟩

theorem viewLsLen_run (a : AState) (h : LsIdx) :
    (viewLsLen h).run a = .ok (a.store.lss.viewLen h, a) := rfl

/-- `ls_node` answers a pair or aborts. -/
theorem lsNodeW_cases (m : Mem) (h : Word) :
    lsNodeW m h = [] ∨ ∃ o l, lsNodeW m h = [o, l] := by
  unfold lsNodeW
  split
  · exact .inl rfl
  split
  · exact .inl rfl
  split
  · exact .inl rfl
  · exact .inr ⟨_, _, rfl⟩

/-- The twin's shape conditions of `reduceProjCore`, against L's word tests. -/
theorem fire_cond_iff (tbl : IProjTable) (i k w6 np nf an usl l4 w3 : Word) (ln : Nat)
    (hk : HW k) (hw6 : HW w6) (hctor : tbl.ctor = decI w6) (hnp : tbl.numParams = np.toNat)
    (hnf : tbl.numFields = nf.toNat)
    (hln : ln = an.toNat) (hlp : tbl.levelParams.length = l4.toNat) :
    (decI k = (tbl.entry i.toNat).ctor ∧ i.toNat < (tbl.entry i.toNat).numFields ∧
      ln = (tbl.entry i.toNat).numParams + (tbl.entry i.toNat).numFields ∧
      usl.toNat = (tbl.entry i.toNat).levelParams.length ∧ (w3 != 0) = true) ↔
    (k = w6 ∧ i < nf ∧ nf ≤ an ∧ an - nf = np ∧ usl = l4 ∧ w3 ≠ 0) := by
  simp only [IProjTable.entry]
  have e1 : (decI k = tbl.ctor) ↔ k = w6 := by
    rw [hctor]; exact ⟨fun h => decI_inj hk hw6 h, fun h => by rw [h]⟩
  have e2 : i.toNat < tbl.numFields ↔ i < nf := by
    rw [hnf]; exact (UInt64.lt_iff_toNat_lt).symm
  have e3 : ln = tbl.numParams + tbl.numFields ↔ (nf ≤ an ∧ an - nf = np) := by
    rw [hln, hnp, hnf, UInt64.le_iff_toNat_le]
    constructor
    · intro h
      refine ⟨by omega, UInt64.toNat_inj.mp ?_⟩
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega))]; omega
    · intro ⟨h1, h2⟩
      have := congrArg UInt64.toNat h2
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr h1)] at this; omega
  have e4 : usl.toNat = tbl.levelParams.length ↔ usl = l4 := by
    rw [hlp]; exact ⟨fun h => UInt64.toNat_inj.mp h, fun h => by rw [h]⟩
  have e5 : (w3 != 0) = true ↔ w3 ≠ 0 := by simp
  rw [e1, e2, e3, e4, e5, and_assoc]

theorem rpFire_refines (p : Prog) (hp : WhnfCoreProg p) (hc : ProjCallees p)
    (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode e1 q i k us : Word) (tbl : IProjTable)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he1 : HW e1) (hk : HW k) (hus : HW us)
    (hq : decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl)
    (hfe : ∃ c, fe.findTable? c = some tbl) (hlt : i.toNat < tbl.numFields)
    (hvus : ∃ (h : EIdx) (c : NIdx), a₀.store.view h = some (.const c (decI us))) :
    GrowSpec p (n + 1) "reduce_proj_fire" [mode, vis, e1, q, i, k, us]
      (rpFireT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1) (decI k) (decI us))
      decOptR s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (rpFire_spec p hp n s₀ mode vis e1 q i k us)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  have hwords := decTbl_words hq hS.erec
  obtain ⟨hlp, hnp, hw6, hctor, hnf⟩ := hwords
  unfold rpFireW at hW
  -- get_app_args
  rcases hc1 : callW p n "get_app_args" [e1] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [hc1, reduceCtorEq] at hW
  obtain ⟨t₁, ht₁, -, hf₁, hg₁, ho₁, htop₁, xs, hxs, hsp₁⟩ := triple_of_callW
    (getAppArgs_spec' p hp.spine n s a₀ hS.arena.1 e1 he1 hS.spn) hc1
  rw [ht₁] at hf₁ hg₁ htop₁ hsp₁
  have hS₁ := hS.frame_stk hf₁ (by simp) (by simp)
  have hE₁ : m₁.arr64 EREC = s.mem.arr64 EREC := hf₁.1 EREC (by simp [SPN, EREC]) (by decide)
  -- ls_node
  rcases hc2 : callW p n "ls_node" [us] m₁ with _ | ⟨r₂, m₂⟩ <;> simp only [hc2, reduceCtorEq] at hW
  obtain ⟨t₂, ht₂, ht₂s, hne₂, hr₂⟩ := triple_of_callW (lsNode_spec p hp.lsn n { s with mem := m₁ } us) hc2
  have hm₂ : m₂ = m₁ := by rw [← ht₂, ht₂s]
  subst hm₂
  obtain ⟨o₂, l₂, hl₂⟩ : ∃ o l, lsNodeW m₂ us = [o, l] := by
    rcases lsNodeW_cases m₂ us with h | h
    · rw [h] at hr₂; exact absurd hr₂ hne₂
    · exact h
  have hr₂' : r₂ = [o₂, l₂] := by rw [hr₂]; exact hl₂
  subst hr₂'
  have hvl : a₀.store.lss.viewLen (decI us) = some l₂.toNat :=
    lsNodeW_viewLen hS₁.arena.1 hus hl₂
  -- fire_ok
  rcases hc3 : callW p n "fire_ok" [q, i, us] m₂ with _ | ⟨r₃, m₃⟩
    <;> simp only [hc3, reduceCtorEq] at hW
  have hq₂ : decTbl (m₂.arr64 EREC) q.toNat = some tbl := by rw [hE₁]; exact hq
  have hfok := hc.fireOk n { s with mem := m₂ } a₀ dn vis fe MM eb q i us tbl hS₁ hus hq₂ hfe hlt hvus
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, -⟩ := CoreSpec.of_callW hfok hc3
  have hE₃ : m₃.arr64 EREC = m₂.arr64 EREC := by
    have := (hc.erec n "fire_ok" [q, i, us] m₂ r₃ m₃ (Or.inr rfl) hc3); exact this
  have hrunF := AM.run_of_ok _ _ hok3
  rw [hres3] at hrunF
  obtain ⟨hlp', hnp', hw6', hctor', hnf'⟩ : tbl.levelParams.length = (rdW (m₃.arr64 EREC) (q + 4)).toNat ∧
      tbl.numParams = (rdW (m₃.arr64 EREC) (q + 5)).toNat ∧ HW (rdW (m₃.arr64 EREC) (q + 6)) ∧
      tbl.ctor = decI (rdW (m₃.arr64 EREC) (q + 6)) ∧
      tbl.numFields = (rdW (m₃.arr64 EREC) (q + 7)).toNat := by
    rw [hE₃, hE₁]; exact ⟨hlp, hnp, hw6, hctor, hnf⟩
  -- the twin up to the shape test
  have hbnd := hsp₁.bound
  have hlen : xs.length = (r₁.tail.headD 0).toNat := by
    have := hsp₁.size; simpa using this
  have hcond := fire_cond_iff tbl i k (rdW (m₃.arr64 EREC) (q + 6)) (rdW (m₃.arr64 EREC) (q + 5))
    (rdW (m₃.arr64 EREC) (q + 7)) (r₁.tail.headD 0) l₂ (rdW (m₃.arr64 EREC) (q + 4)) (r₃.headD 0)
    xs.length hk hw6' hctor' hnp' hnf' hlen hlp'
  have hdb : decBool r₃ = (r₃.headD 0 != 0) := rfl
  have hpreP : (decI k = (tbl.entry i.toNat).ctor ∧ i.toNat < (tbl.entry i.toNat).numFields ∧
          xs.length = (tbl.entry i.toNat).numParams + (tbl.entry i.toNat).numFields ∧
          l₂.toNat = (tbl.entry i.toNat).levelParams.length ∧ (r₃.headD 0 != 0) = true) →
      (rpFireT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1) (decI k) (decI us)).run a₀ =
        (rpArgT fe (decMode mode).verifiedChecks (decI k) xs
            ((tbl.entry i.toNat).numParams + i.toNat)).run (AM.st ((tbl.entry i.toNat).fireOk (decI us)) a₀) := by
    intro h
    simp only [rpFireT, StateT.run_bind, hxs, except_ok_bind, viewLsLen_run, hvl, hrunF, hdb]
    rw [ite_eq_left h]
  have hpreN : ¬ (decI k = (tbl.entry i.toNat).ctor ∧ i.toNat < (tbl.entry i.toNat).numFields ∧
          xs.length = (tbl.entry i.toNat).numParams + (tbl.entry i.toNat).numFields ∧
          l₂.toNat = (tbl.entry i.toNat).levelParams.length ∧ (r₃.headD 0 != 0) = true) →
      (rpFireT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1) (decI k) (decI us)).run a₀ =
        (pure none : AM (Option EIdx)).run (AM.st ((tbl.entry i.toNat).fireOk (decI us)) a₀) := by
    intro h
    simp only [rpFireT, StateT.run_bind, hxs, except_ok_bind, viewLsLen_run, hvl, hrunF, hdb]
    rw [ite_eq_right h]
  by_cases hLc : k = rdW (m₃.arr64 EREC) (q + 6) ∧ i < rdW (m₃.arr64 EREC) (q + 7) ∧
      rdW (m₃.arr64 EREC) (q + 7) ≤ r₁.tail.headD 0 ∧
      r₁.tail.headD 0 - rdW (m₃.arr64 EREC) (q + 7) = rdW (m₃.arr64 EREC) (q + 5) ∧
      ([o₂, l₂] : List Word).tail.headD 0 = rdW (m₃.arr64 EREC) (q + 4) ∧ r₃.headD 0 ≠ 0
  · rw [ite_eq_left hLc] at hW
    have hTc := hcond.mpr hLc
    have hpre := hpreP hTc
    cases hc4 : callW p n "reduce_proj_arg" [mode, vis, k, r₁.headD 0, r₁.tail.headD 0,
        rdW (m₃.arr64 EREC) (q + 5) + i] m₃ with
    | none => simp only [hc4] at hW; cases hW
    | some q₄ =>
    obtain ⟨r₄, m₄⟩ := q₄
    simp only [hc4, Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    cases n with
    | zero => simp [callW_zero] at hc4
    | succ N =>
    have hao : (r₁.headD 0).toNat + (r₁.tail.headD 0).toNat ≤ (spTop m₂).toNat := by
      have h1 := hsp₁.bound
      have h2 := hS₁.spn
      rw [htop₁, UInt64.toNat_add, Nat.mod_eq_of_lt (by rw [← ho₁]; omega), ← ho₁]
      exact Nat.le_refl _
    have hspR : SpineR m₃ (r₁.headD 0) (r₁.tail.headD 0) xs.toArray :=
      hsp₁.keep hSt₃.size hSt₃.below hao hS₁.spn
    have hjn : (rdW (m₃.arr64 EREC) (q + 5) + i).toNat = tbl.numParams + i.toNat := by
      have hlt := UInt64.lt_iff_toNat_lt.mp hLc.2.1
      have hle := UInt64.le_iff_toNat_le.mp hLc.2.2.1
      have heq := congrArg UInt64.toNat hLc.2.2.2.1
      rw [UInt64.toNat_sub_of_le _ _ hLc.2.2.1] at heq
      have han := (r₁.tail.headD 0).toNat_lt
      rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), ← hnp']
    have harg := rpArg_refines p hp N { s with mem := m₃ }
      (AM.st ((tbl.entry i.toNat).fireOk (decI us)) a₀)
      dn vis fe M₃ eb mode k (r₁.headD 0) (r₁.tail.headD 0) (rdW (m₃.arr64 EREC) (q + 5) + i)
      xs.toArray ⟨hS₃, hs.mode4, hs.eb_mode⟩ hk hspR
    obtain ⟨hok4, ⟨M₄, hS₄, hK₄, hSt₄⟩, hres4, hrw4⟩ := CoreSpec.of_callW harg hc4
    have e1 : xs.toArray.toList = xs := rfl
    rw [e1, hjn] at hok4 hres4 hS₄
    have hrun4 := AM.run_of_ok _ _ hok4
    rw [hres4] at hrun4
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hpre.trans hrun4)
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]
      exact ⟨M₄, hS₄, hK₃.trans hK₄, (hg₁.trans hSt₃.toGrew).trans hSt₄.toGrew⟩
    · rw [hres]; unfold decOptR; rw [← hr0, ← hr1]
    · unfold ResW; rw [← hr0, ← hr1]; exact hrw4
  · rw [ite_eq_right hLc] at hW
    have hTc : ¬ (decI k = (tbl.entry i.toNat).ctor ∧ i.toNat < (tbl.entry i.toNat).numFields ∧
          xs.length = (tbl.entry i.toNat).numParams + (tbl.entry i.toNat).numFields ∧
          l₂.toNat = (tbl.entry i.toNat).levelParams.length ∧ (r₃.headD 0 != 0) = true) :=
      fun h => hLc (hcond.mp h)
    have hpre := hpreN hTc
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hpre
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact ⟨M₃, hS₃, hK₃, hg₁.trans hSt₃.toGrew⟩
    · rw [hres]; unfold decOptR; rw [← hr0]; rfl
    · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, by unfold HW; decide⟩

/-! ## `reduce_proj_head` -/

theorem decE_const_tag (h : Word) (hh : HW h) : ((decE h).tag == ETag.const) = (h >>> 28 == 3) := by
  rw [decE_tag h hh, ETag.const]
  rw [show (3 : UInt32) = (3 : Word).toUInt32 from rfl]
  exact toUInt32_beq _ _ (shr28_lt h hh) (by decide)

/-- **A `const` node past the view checks**: its name and level-list handles are the record's
words. -/
theorem view_const_words (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) (hg : h >>> 28 = 3) :
    ∃ n us, a.store.view (decE h) = some (.const n us) ∧
      n = decI (tfld m CONST (tierW h) (idxW h) 0) ∧
      us = decI (tfld m CONST (tierW h) (idxW h) 1) ∧
      HW (tfld m CONST (tierW h) (idxW h) 0) ∧
      HW (tfld m CONST (tierW h) (idxW h) 1) := by
  obtain ⟨k, hk, hkr⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  obtain ⟨h1, h2⟩ := hkr
  refine ⟨k.n, k.us, ?_, ?_, ?_, ?_, ?_⟩
  · rw [view_tier m a hR h hh hv.1, get_const _ h hh hg, Tbl.node?, hk]; rfl
  · rw [h1, decI_word]
  · rw [h2, decI_word]
  · rw [h1]; unfold HW; rw [UInt32.toNat_toUInt64]; exact k.n.word.toNat_lt
  · rw [h2]; unfold HW; rw [UInt32.toNat_toUInt64]; exact k.us.word.toNat_lt

/-- The twin from the scrutinee's head on. -/
def rpHeadT (mode : ConLeche.CheckMode) (fe : IFEnv) (entry : IProjEntry) (i : Nat) (e' : EIdx) :
    AM (Option EIdx) := do
  let hh ← getAppFn coreWalkFuel e'
  if hh.tag == ETag.const then
    match ← view hh with
    | .const k us => rpFireT mode fe entry i e' k us
    | _ => pure none
  else pure none

/-- The model of `reduce_proj_head`. -/
def rpHeadW (p : Prog) (n : Nat) (m : Mem) (mode vis e1 q i : Word) : Option (Word × Word × Mem) :=
  match callW p n "get_app_fn" [e1] m with
  | none => none
  | some (r₁, m₁) =>
    if r₁.headD 0 >>> 28 ≠ 3 then some (0, 0, m₁)
    else if tierW (r₁.headD 0) ≠ 0 ∧ rdW (m₁.arr64 CTL) 1 = 0 then none
    else if tcnt m₁ CONST (tierW (r₁.headD 0)) ≤ idxW (r₁.headD 0) then none
    else match callW p n "reduce_proj_fire" [mode, vis, e1, q, i,
        tfld m₁ CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0,
        tfld m₁ CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 1] m₁ with
      | none => none
      | some (r₂, m₂) => some (r₂.headD 0, r₂.tail.headD 0, m₂)

theorem rpHead_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (mode vis e1 q i : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_proj_head" [mode, vis, e1, q, i]
    ⦃fun r s' => LocEq s' s₀ ∧
      rpHeadW p n s₀.mem mode vis e1 q i = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.rphead]
  simp only [callFn, reduceProjHeadL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "get_app_fn", callW_spec p n "reduce_proj_fire"] <;>
    finish [rpHeadW, tierW, idxW]

theorem rpHead_refines (p : Prog) (hp : WhnfCoreProg p) (hc : ProjCallees p)
    (n : Nat)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode e1 q i : Word) (tbl : IProjTable)
    (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (he1 : HW e1)
    (hq : decTbl (s₀.mem.arr64 EREC) q.toNat = some tbl)
    (hfe : ∃ c, fe.findTable? c = some tbl) (hlt : i.toNat < tbl.numFields) :
    GrowSpec p (n + 1) "reduce_proj_head" [mode, vis, e1, q, i]
      (rpHeadT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1))
      decOptR s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (rpHead_spec p hp n s₀ mode vis e1 q i)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold rpHeadW at hW
  rcases hc1 : callW p n "get_app_fn" [e1] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [hc1, reduceCtorEq] at hW
  obtain ⟨t₁, ht₁, hm₁, -, hhw, hrun1⟩ := triple_of_callW
    (getAppFn_refines p hp.spine n s a₀ hS.arena.1 e1 he1) hc1
  have hm₁' : m₁ = s.mem := by rw [← ht₁]; exact hm₁
  subst hm₁'
  by_cases g : r₁.headD 0 >>> 28 ≠ 3
  · rw [ite_eq_left g] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    have hT : (rpHeadT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1)).run a₀ =
        .ok (none, a₀) := by
      have hb : (r₁.headD 0 >>> 28 == 3) = false := by simpa using g
      simp only [rpHeadT, StateT.run_bind, hrun1, except_ok_bind, decE_const_tag _ hhw, hb]
      rfl
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact ⟨MM, hS, KeptAll.refl _ _, (StackKept.refl _).toGrew⟩
    · rw [hres]; unfold decOptR; rw [← hr0]; rfl
    · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, by unfold HW; decide⟩
  rw [ite_eq_right g] at hW
  have g3 : r₁.headD 0 >>> 28 = 3 := by simpa using g
  obtain ⟨hsc, hW⟩ := of_ite_none hW
  obtain ⟨hbd, hW⟩ := of_ite_none hW
  have hvOK : viewOK s.mem (r₁.headD 0) CONST := ⟨hsc, by simpa using hbd⟩
  obtain ⟨n', us', hv, hn, hus, hhn, hhus⟩ := view_const_words s.mem a₀ hS.arena.1 (r₁.headD 0)
    hhw hvOK g3
  cases hc2 : callW p n "reduce_proj_fire" [mode, vis, e1, q, i,
      tfld s.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0,
      tfld s.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 1] s.mem with
  | none => rw [hc2] at hW; cases hW
  | some q₂ =>
  obtain ⟨r₂, m₂⟩ := q₂
  simp only [hc2, Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr0, hr1, hm⟩ := hW
  cases n with
  | zero => simp [callW_zero] at hc2
  | succ N =>
  have hfire := rpFire_refines p hp hc N s a₀ dn vis fe MM eb mode e1 q i _ _ tbl hs he1 hhn hhus hq hfe hlt
    ⟨_, n', by rw [hv, hus]⟩
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, hrw2⟩ := GrowSpec.of_callW hfire hc2
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hrun2
  have hT : (rpHeadT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1)).run a₀ =
      (rpFireT (decMode mode) fe (tbl.entry i.toNat) i.toNat (decE e1)
        (decI (tfld s.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 0))
        (decI (tfld s.mem CONST (tierW (r₁.headD 0)) (idxW (r₁.headD 0)) 1))).run a₀ := by
    have hb : (r₁.headD 0 >>> 28 == 3) = true := by simpa using g3
    simp only [rpHeadT, StateT.run_bind, hrun1, except_ok_bind, decE_const_tag _ hhw, hb, ite_true,
      view_run _ _ _ hv]
    rw [hn, hus]
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans hrun2)
  refine ⟨hok, ?_, ?_, ?_⟩
  · rw [hst, ← hm]; exact ⟨M₂, hS₂, hK₂, hSt₂⟩
  · rw [hres]; unfold decOptR; rw [← hr0, ← hr1]
  · unfold ResW; rw [← hr0, ← hr1]; exact hrw2

/-! ## `reduce_proj_core` pieces -/

/-- The twin, cut as `projLitToCtor`, the table lookup, then `rpHeadT`. -/
def rpCoreT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (sn : NIdx)
    (i : Nat) (c : EIdx) : AM (Option EIdx) := do
  let e' ← projLitToCtor r fe depth c
  match fe.findProj? sn i with
  | some entry => rpHeadT mode fe entry i e'
  | none => pure none

theorem reduceProjCore_eq (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat)
    (sn : NIdx) (i : Nat) (c : EIdx) :
    reduceProjCore mode r fe depth sn i c = rpCoreT mode r fe depth sn i c := rfl

/-- The model of `reduce_proj_core`. -/
def rpCoreW (p : Prog) (n : Nat) (m : Mem) (mode vis d sn i c : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "proj_lit_to_ctor" [mode, vis, d, c] m with
  | none => none
  | some (r₁, m₁) =>
    match callW p n "find_proj" [vis, sn, i] m₁ with
    | none => none
    | some (r₂, m₂) =>
      if r₂.headD 0 = 0 then some (0, 0, m₂)
      else match callW p n "reduce_proj_head" [mode, vis, r₁.headD 0, r₂.tail.headD 0, i] m₂ with
        | none => none
        | some (r₃, m₃) =>
          if 136 < (m₃.arr64 CTL).size then
            some (r₃.headD 0, r₃.tail.headD 0, m₃.set64 CTL 136 (rdW (m.arr64 CTL) 136))
          else none

theorem rpCore_spec (p : Prog) (hp : WhnfCoreProg p) (n : Nat) (s₀ : St) (mode vis d sn i c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "reduce_proj_core" [mode, vis, d, sn, i, c]
    ⦃fun r s' => LocEq s' s₀ ∧
      rpCoreW p n s₀.mem mode vis d sn i c = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.rproj]
  simp only [callFn, reduceProjCoreL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "proj_lit_to_ctor", callW_spec p n "find_proj",
    callW_spec p n "reduce_proj_head"] <;>
  simp_all [rpCoreW, Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil,
    Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr, rdW, CTL] <;>
  (congr 1; rw [Array.getElem?_eq_getElem]; rfl)

/-! ## `reduce_proj_core` -/

/-- **`reduce_proj_core` refines `reduceProjCore`.** -/
theorem reduceProjCore_refines' (p : Prog) (hp : WhnfCoreProg p) (hStrSup : StrLitSupportedOK p)
    (hStrCtor : StrLitCtorOK p) (hc : ProjCallees p)
    (_hl : p.lookup "ls_node" = some lsNode) (hE : ErecKept p) (n : Nat)
    (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps)
    (eb mode d sn i c : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode) (hsn : HW sn) (hc' : HW c)
    (hsup : SupKeep fe) :
    CoreSpec p (n + 1) "reduce_proj_core" [mode, vis, d, sn, i, c]
      (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI sn) i.toNat
        (decE c)) decOptR s₀ a₀ dn vis fe MM eb ResW := by
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (rpCore_spec p hp n s₀ mode vis d sn i c)
  subst hs0
  refine ⟨hloc, ?_⟩
  have hS := hs.rel
  unfold rpCoreW at hW
  cases n with
  | zero => simp [callW_zero] at hW
  | succ N =>
  rcases hc1 : callW p (N + 1) "proj_lit_to_ctor" [mode, vis, d, c] s.mem with _ | ⟨r₁, m₁⟩
    <;> simp only [hc1, reduceCtorEq] at hW
  have hplit := projLitToCtor_refines' p hp hStrSup hStrCtor N (hk.mono (by omega)) F (by omega) (by omega) s a₀
    dn vis fe MM eb mode d c hs hc' hsup
  obtain ⟨hok1, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres1, hrw1⟩ := CoreSpec.of_callW hplit hc1
  have hrun1 := AM.run_of_ok _ _ hok1
  rw [hres1] at hrun1
  rcases hc2 : callW p (N + 1) "find_proj" [vis, sn, i] m₁ with _ | ⟨r₂, m₂⟩
    <;> simp only [hc2, reduceCtorEq] at hW
  have hfp := hc.findProj (N + 1) { s with mem := m₁ } _ dn vis fe M₁ eb sn i hS₁ hsn
  obtain ⟨hok2, ⟨M₂, hS₂, hK₂, hSt₂⟩, hres2, -⟩ := CoreSpec.of_callW hfp hc2
  have hE₂ : m₂.arr64 EREC = m₁.arr64 EREC := hE (N + 1) "find_proj" [vis, sn, i] m₁ r₂ m₂ (Or.inl rfl) hc2
  have hfx : fe.findProj? (decI sn) i.toNat =
      decEntry (m₁.arr64 EREC) (r₂.headD 0) (r₂.tail.headD 0) i.toNat := hres2
  by_cases hf : r₂.headD 0 = 0
  · rw [ite_eq_left hf] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    have hde : decEntry (m₁.arr64 EREC) (r₂.headD 0) (r₂.tail.headD 0) i.toNat = none := by
      unfold decEntry; rw [ite_eq_left hf]
    rw [hde] at hfx
    have hT : (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI sn) i.toNat (decE c)).run a₀ =
        (pure none : AM (Option EIdx)).run
          (AM.st (projLitToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE c)) a₀) := by
      rw [reduceProjCore_eq]
      simp only [rpCoreT, StateT.run_bind, hrun1, except_ok_bind, hfx]
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ (hT.trans rfl)
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact ⟨M₂, hS₂, hK₁.trans hK₂, hSt₁.trans hSt₂⟩
    · rw [hres]; unfold decOptR; rw [← hr0]; rfl
    · unfold ResW; rw [← hr0, ← hr1]; exact ⟨by unfold HW; decide, by unfold HW; decide⟩
  rw [ite_eq_right hf] at hW
  obtain ⟨tbl, hdt, hfe⟩ := hc.projFound (N + 1) m₁ _ dn vis fe M₁ eb sn i r₂ m₂ hS₁ hc2 hf
  have hde : decEntry (m₁.arr64 EREC) (r₂.headD 0) (r₂.tail.headD 0) i.toNat =
      some (tbl.entry i.toNat) := by
    unfold decEntry; rw [ite_eq_right hf, hdt]; rfl
  rw [hde] at hfx
  have hq : decTbl (m₂.arr64 EREC) (r₂.tail.headD 0).toNat = some tbl := by rw [hE₂]; exact hdt
  rcases hc3 : callW p (N + 1) "reduce_proj_head" [mode, vis, r₁.headD 0, r₂.tail.headD 0, i] m₂ with _ | ⟨r₃, m₃⟩
    <;> simp only [hc3, reduceCtorEq] at hW
  have hhead := rpHead_refines p hp hc N { s with mem := m₂ } _ dn vis fe M₂ eb mode (r₁.headD 0)
    (r₂.tail.headD 0) i tbl ⟨hS₂, hs.mode4, hs.eb_mode⟩ hrw1 hq hfe
    (by simpa [IProjTable.entry] using findProj?_lt hfx)
  obtain ⟨hok3, ⟨M₃, hS₃, hK₃, hSt₃⟩, hres3, hrw3⟩ := GrowSpec.of_callW hhead hc3
  have hrun3 := AM.run_of_ok _ _ hok3
  rw [hres3] at hrun3
  by_cases h136 : 136 < (m₃.arr64 CTL).size
  · rw [ite_eq_left h136] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr0, hr1, hm⟩ := hW
    have hT : (reduceProjCore (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI sn) i.toNat (decE c)).run a₀ =
        .ok (decOptR r₃, AM.st (rpHeadT (decMode mode) fe (tbl.entry i.toNat) i.toNat
          (decE (r₁.headD 0)))
            (AM.st (projLitToCtor (coreKnot (decMode mode) fe id F) fe d.toNat (decE c)) a₀)) := by
      rw [reduceProjCore_eq]
      simp only [rpCoreT, StateT.run_bind, hrun1, except_ok_bind, hfx, decH]
      exact hrun3
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hT
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]
      refine ⟨M₃, hS₃.frame_stk (MemFrame.setCtl m₃ 136 _) (by simp) (by simp),
        hK₁.trans (hK₂.trans hK₃), ?_⟩
      have t1 : spTop m₁ = spTop s.mem := hSt₁.1
      have t2 : spTop m₂ = spTop m₁ := hSt₂.1
      apply StackKept.restore _ (by rw [hSt₃.size, hSt₂.size, hSt₁.size])
        (hSt₁.bstk.trans (hSt₂.bstk.trans hSt₃.bstk)) (hSt₁.pool.trans (hSt₂.pool.trans hSt₃.pool)) h136
      intro j hj
      have hj2 : j < spTop m₂ := by rw [t2, t1]; exact hj
      have hj1 : j < spTop m₁ := by rw [t1]; exact hj
      rw [hSt₃.below j hj2]
      exact (hSt₂.below j hj1).trans (hSt₁.below j hj)
    · rw [hres]; unfold decOptR; rw [← hr0, ← hr1]
    · unfold ResW; rw [← hr0, ← hr1]; exact hrw3
  · rw [ite_eq_right h136] at hW; cases hW

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
theorem whnfCoreStepProj_refines' (p : Prog) (hp : WhnfCoreProg p) (hStrSup : StrLitSupportedOK p)
    (hStrCtor : StrLitCtorOK p) (hc : ProjCallees p)
    (hl : p.lookup "ls_node" = some lsNode) (hE : ErecKept p) (n : Nat)
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
    · rw [ite_eq_right (by simpa using hch)] at hcall
      have hslot := (hk n (Nat.le_refl n)).whnf F s a₀ dn vis fe MM eb mode d pe hF hn hs hpe
      obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hslot hcall
      refine ⟨M₁, _, hS₁, hK₁, hSt₁, hrw, ?_⟩
      have := AM.run_of_ok _ _ hok
      rw [hres] at this
      rw [ite_eq_right (by simp [hch])]; exact this
    · rw [ite_eq_left hch] at hcall
      have hslot := (hk n (Nat.le_refl n)).whnfCore F s a₀ dn vis fe MM eb mode 1 d pe hF hn hs hpe
      obtain ⟨hok, ⟨M₁, hS₁, hK₁, hSt₁⟩, hres, hrw⟩ := CoreSpec.of_callW hslot hcall
      refine ⟨M₁, _, hS₁, hK₁, hSt₁, hrw, ?_⟩
      have := AM.run_of_ok _ _ hok
      rw [hres] at this
      rw [ite_eq_left (by simpa using hch)]; exact this
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
  have hred := reduceProjCore_refines' p hp hStrSup hStrCtor hc hl hE N (hk.mono (by omega)) F (by omega)
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
    · rw [ite_eq_right (by simpa using hf)] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨h0, h1, hm⟩ := hW
      exact ⟨fun h => absurd hf h, fun _ => ⟨h0.symm, h1.symm⟩, hm⟩
    · rw [ite_eq_left (by simpa using hf)] at hW
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

end wrap

end L.Arena
