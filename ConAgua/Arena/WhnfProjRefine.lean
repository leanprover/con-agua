import ConAgua.Arena.WhnfProj
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.PromoteNRef
import ConAgua.Arena.PromoteLsRef
import ConRon.Arena.WFProofs

/-!
# `proj_table_name` refines `projTableName` under `CoreS` (lane `whnf3`, helper `whnf3-proj`)

* **The twin's name step** (`internNNode_nstep`): a run of `internNNode v` is the state with the
  name store replaced by `(ns.intern v).1` (a hit leaves it as it was), at the handle
  `(ns.intern v).2`; with `NStoreWF` and `ViewOK v` it keeps `NStoreWF`, extends the name store,
  and the level and level-list stores extend with it (`LExt.of_view_mono`).
* **`CoreS` across a name interning** (`CoreS.of_name`): as `CoreS.of_level`, the twin's step a
  `NameStep`, the memory writes confined to the store arrays below 42.
* **The pool bytes**: nine words written at the top and the top raised past them is a `Grows`
  (`grows_poolSet`, `grows_top`), across which `CoreS` holds (`CoreS.arena_frame`, `ArenaD.grow`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false

namespace L.Arena

/-! ## The twin's name step -/

/-- The state with the name store replaced. -/
def withNs (a : AState) (ns : NStore) : AState :=
  { a with store := { a.store with lss := { a.store.lss with ls := { a.store.lss.ls with ns := ns } } } }

theorem nstore_find_none_intern {st : NStore} {v : NNodeView} (hf : st.find? v = none) :
    st.intern v = (if st.scratchOn then
        ({ st with scr := (st.scr.push v (st.derOfView v) Idx.tierS).1 },
          (st.scr.push v (st.derOfView v) Idx.tierS).2)
      else ({ st with pers := (st.pers.push v (st.derOfView v) Idx.tierP).1 },
          (st.pers.push v (st.derOfView v) Idx.tierP).2)) := by
  simp only [NStore.find?] at hf
  simp only [NStore.intern]
  split
  · rename_i i hp; rw [hp] at hf; cases hf
  · rename_i hp
    rw [hp] at hf
    by_cases hon : st.scratchOn = true
    · simp only [hon, ite_true] at hf ⊢
      rw [hf]
    · simp only [hon, Bool.false_eq_true, ite_false]

theorem nstore_find_some_intern {st : NStore} {v : NNodeView} {i : NIdx} (hf : st.find? v = some i) :
    st.intern v = (st, i) := by
  simp only [NStore.find?] at hf
  simp only [NStore.intern]
  split
  · rename_i j hp; rw [hp] at hf; exact congrArg _ (Option.some.inj hf)
  · rename_i hp
    rw [hp] at hf
    by_cases hon : st.scratchOn = true
    · simp only [hon, ite_true] at hf ⊢
      rw [hf]
    · simp only [hon, Bool.false_eq_true, ite_false] at hf; cases hf

theorem run_get_bind' {β : Type} (f : AState → AM β) (lst : AState) :
    ((do let s ← get; f s : AM β)).run lst = (f lst).run lst := rfl

/-- **A run of `internNNode v`** is the name store's `intern`, at the capacity it checks. -/
theorem internNNode_run_eq {v : NNodeView} {a a' : AState} {h : NIdx}
    (hrun : (internNNode v).run a = .ok (h, a')) :
    h = (a.store.lss.ls.ns.intern v).2 ∧ a' = withNs a (a.store.lss.ls.ns.intern v).1 ∧
      (a.store.lss.ls.ns.find? v = none → a.store.lss.ls.ns.capOK v) := by
  simp only [internNNode, run_get_bind'] at hrun
  cases hf : a.store.ns.find? v with
  | some i =>
    have hf' : a.store.lss.ls.ns.find? v = some i := hf
    rw [hf] at hrun
    simp only [pure, StateT.pure, StateT.run, Except.ok.injEq, Prod.mk.injEq] at hrun
    obtain ⟨rfl, rfl⟩ := hrun
    rw [nstore_find_some_intern hf']
    refine ⟨rfl, rfl, fun h' => by rw [hf'] at h'; cases h'⟩
  | none =>
    rw [hf] at hrun
    by_cases hcap : (if a.store.ns.scratchOn then a.store.ns.scr.sizeOf v
        else a.store.ns.pers.sizeOf v) < Idx.idxCap
    · rw [ite_eq_left hcap] at hrun
      simp only [EStore.internName, LsStore.internName, LStore.internName, set, StateT.set,
        StateT.run_bind, pure, StateT.pure, bind, StateT.bind, StateT.run, Except.ok.injEq,
        Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      refine ⟨rfl, rfl, fun _ => ?_⟩
      unfold NStore.capOK; exact hcap
    · rw [ite_eq_right hcap] at hrun
      simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, bind,
        Except.bind] at hrun

/-- **What a name interning keeps**: everything but the name store, which it extends. -/
structure NameStep (a a' : AState) : Prop where
  caches : a'.caches = a.caches
  pins : a'.pins = a.pins
  pers : a'.store.pers = a.store.pers
  scr : a'.store.scr = a.store.scr
  lsp : a'.store.lss.pers = a.store.lss.pers
  lss : a'.store.lss.scr = a.store.lss.scr
  lon : a'.store.lss.scratchOn = a.store.lss.scratchOn
  lp : a'.store.lss.ls.pers = a.store.lss.ls.pers
  ls : a'.store.lss.ls.scr = a.store.lss.ls.scr
  lon2 : a'.store.lss.ls.scratchOn = a.store.lss.ls.scratchOn
  nwf : NStoreWF a'.store.lss.ls.ns
  next : NExt a.store.lss.ls.ns a'.store.lss.ls.ns

theorem internNNode_nstep {v : NNodeView} {a a' : AState} {h : NIdx}
    (hwf : NStoreWF a.store.lss.ls.ns) (hv : a.store.lss.ls.ns.ViewOK v)
    (hrun : (internNNode v).run a = .ok (h, a')) :
    NameStep a a' ∧ a'.store.lss.ls.ns.view h = some v := by
  obtain ⟨rfl, rfl, hcap⟩ := internNNode_run_eq hrun
  have key : NStoreWF (a.store.lss.ls.ns.intern v).1 ∧
      (a.store.lss.ls.ns.intern v).1.view (a.store.lss.ls.ns.intern v).2 = some v := by
    cases hf : a.store.lss.ls.ns.find? v with
    | none =>
      have := NStore.intern_spec hwf hv (hcap hf)
      exact ⟨this.1, this.2.2⟩
    | some i =>
      rw [nstore_find_some_intern hf]
      exact ⟨hwf, NStore.view_of_find hwf hf⟩
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, key.1, NStore.intern_ext _ _⟩, key.2⟩

theorem NameStep.lext {a a' : AState} (h : NameStep a a') : LExt a.store.lss.ls a'.store.lss.ls := by
  refine LExt.of_view_mono h.next (fun i w hw => ?_) ?_
  · have e : a'.store.lss.ls.view i = a.store.lss.ls.view i := by
      simp only [LStore.view, h.lp, h.ls, h.lon2]
    rw [e]; exact hw
  · simp only [LStore.nodeCount, LStore.persCount, LStore.scrCount, h.lp, h.ls, Nat.le_refl]

theorem NameStep.lsext {a a' : AState} (h : NameStep a a') : LsExt a.store.lss a'.store.lss := by
  refine LsExt.of_view_mono h.lext (fun i w hw => ?_)
  have e : a'.store.lss.view i = a.store.lss.view i := by
    simp only [LsStore.view, h.lsp, h.lss, h.lon]
  rw [e]; exact hw

theorem NameStep.trans {a b c : AState} (h₁ : NameStep a b) (h₂ : NameStep b c) : NameStep a c :=
  ⟨h₂.caches.trans h₁.caches, h₂.pins.trans h₁.pins, h₂.pers.trans h₁.pers, h₂.scr.trans h₁.scr,
    h₂.lsp.trans h₁.lsp, h₂.lss.trans h₁.lss, h₂.lon.trans h₁.lon, h₂.lp.trans h₁.lp,
    h₂.ls.trans h₁.ls, h₂.lon2.trans h₁.lon2, h₂.nwf, fun i n hn => h₂.next i n (h₁.next i n hn)⟩

/-- **`CoreS` across name interning** whose memory writes are confined to the store's arrays
(below 42) and counts (`CTL` below 42). -/
theorem CoreS.of_name {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hN : NameStep a a') (hR : ArenaR m' a')
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42) (hC : ∀ x ∈ C, x.toNat < 42) :
    CoreS dn m' a' vis fe M eb := by
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => .inl (hA b hb)) a hS.arena.2) hN.pers hN.scr
  refine ⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
      (fun x hx => .inl (by have := hC x hx; omega)) hf, ?_, ?_, hN.nwf,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
      hS.memos.frame hf ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩,
      hf.2.2.1 145 ▸ hS.bstk⟩
  · rw [hN.caches]
    exact CoreRM.frame (A := A) (C := C) (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
      (fun x hx => .inl (by have := hC x hx; omega)) hf hS.core
  · rw [hN.pins]
    exact hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp only [PINS, ArrId] at this; omega)
      (by decide))
  · intro h l e
    rw [hN.caches] at e
    exact hN.lext.lvl h l (hS.readL h l e)
  · intro h l e
    rw [hN.caches] at e
    exact hN.lsext.lst h l (hS.readLs h l e)

/-! ## The programs -/

/-- **The lookups the projection functions need.** -/
structure ProjProg (p : Prog) : Prop where
  ptn : p.lookup "proj_table_name" = some projTableNameL
  findProj : p.lookup "find_proj" = some findProjL
  fireOk : p.lookup "fire_ok" = some fireOkL
  litHash : p.lookup "lit_hash" = some litHash
  limbsEq : p.lookup "limbs_eq" = some limbsEq
  nsMatch : p.lookup "nstr_match" = some nsMatch
  nsFind : p.lookup "nstr_find" = some nsFind
  nsPush : p.lookup "nstr_push" = some nsPush
  nstr : p.lookup "intern_nstr" = some internNStr
  nnFind : p.lookup "nnum_find" = some nnumFind
  nnPush : p.lookup "nnum_push" = some nnumPush
  nnum : p.lookup "intern_nnum" = some internNNum
  envix : p.lookup "env_ix" = some envIxL
  envrow : p.lookup "env_row_get" = some envRowGetL
  envfind : p.lookup "env_find" = some envFindL

/-! ## `proj_table_name`: the word model -/

/-- The nine bytes of `"projTable"` written at `o`. -/
def ptBytes (m : Mem) (o : Word) : Mem :=
  (((((((((m.set64 POOL o 112).set64 POOL (o + 1) 114).set64 POOL (o + 2) 111).set64 POOL (o + 3) 106).set64
    POOL (o + 4) 84).set64 POOL (o + 5) 97).set64 POOL (o + 6) 98).set64 POOL (o + 7) 108).set64 POOL
    (o + 8) 101)

/-- The memory `intern_nstr` sees: the bytes, the top raised past them. -/
def ptMem (m : Mem) (o : Word) : Mem := (ptBytes m o).set64 CTL 0 (o + 9)

/-- The model of `proj_table_name`. -/
def ptnW (p : Prog) (n : Nat) (m : Mem) (t : Word) : Option (Word × Mem) :=
  if 4294967295 < t then none
  else if (2 : Word) < (t >>> 28) then none
  else if ((t >>> 27) &&& 1) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if rdW (m.arr64 CTL) ((34 : Word) + (t >>> (28 : Word)) * (2 : Word) + ((t >>> (27 : Word)) &&& 1)) ≤ (t &&& 134217727) then none
  else if rdW (m.arr64 CTL) 0 + 9 < rdW (m.arr64 CTL) 0 then none
  else if m.len64 POOL < rdW (m.arr64 CTL) 0 + 9 then none
  else match callW p n "intern_nstr" [t, rdW (m.arr64 CTL) 0, 9] (ptMem m (rdW (m.arr64 CTL) 0)) with
    | none => none
    | some (r₁, m₁) =>
      if 4294967296 ≤ r₁.headD 0 then none
      else match callW p n "intern_nnum" [r₁.headD 0, 0] m₁ with
        | none => none
        | some (r₂, m₂) => some (r₂.headD 0, m₂)

theorem projTableName_spec (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_table_name" [t]
    ⦃fun r s' => LocEq s' s₀ ∧ ptnW p n s₀.mem t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ptn]
  simp only [callFn, projTableNameL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "intern_nstr", callW_spec p n "intern_nnum"] <;>
    finish [ptnW, ptMem, ptBytes]

end L.Arena
