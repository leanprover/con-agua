import ConAgua.Arena.WhnfProj
import ConAgua.Arena.CoreWalks
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
  son : a'.store.scratchOn = a.store.scratchOn

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
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, key.1, NStore.intern_ext _ _, rfl⟩, key.2⟩

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
    h₂.ls.trans h₁.ls, h₂.lon2.trans h₁.lon2, h₂.nwf, fun i n hn => h₂.next i n (h₁.next i n hn),
    h₂.son.trans h₁.son⟩

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
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide),
          fun h => absurd (hA _ h) (by decide)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide),
          fun h => absurd (hA _ h) (by decide)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩,
      hf.2.2.1 145 ▸ hS.bstk,
      hS.den.mono hN.lsext (by rw [hN.pins]) (by rw [hN.pins]) (fun _ _ hk => .inl (hN.caches ▸ hk))
        (fun x u hv => by simpa only [EStore.view, hN.pers, hN.scr, hN.son] using hv)
        (fun x c us hv => .inl (by simpa only [EStore.view, hN.pers, hN.scr, hN.son] using hv))
        (hS.den.lvlAll.of_lext (fun u hu => by
          have e : a'.store.ls.view u = a.store.ls.view u := by
            show a'.store.lss.ls.view u = a.store.lss.ls.view u
            unfold LStore.view; rw [hN.lp, hN.ls, hN.lon2]
          rw [← e]; exact hu) hN.lext)
        (hS.den.lsAll.of_ext (fun u hu => by
          have e : a'.store.lss.view u = a.store.lss.view u := by
            unfold LsStore.view; rw [hN.lsp, hN.lss, hN.lon]
          rw [← e]; exact hu) hN.lsext)⟩
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

theorem ptnW_spec (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_table_name" [t]
    ⦃fun r s' => LocEq s' s₀ ∧ ptnW p n s₀.mem t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ptn]
  simp only [callFn, projTableNameL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, evalE_tierE, evalE_idxE,
      callW_spec p n "intern_nstr", callW_spec p n "intern_nnum"] <;>
    finish [ptnW, ptMem, ptBytes, tierW, idxW]

/-! ## The pool bytes -/

/-- A pool write above the original top, after a growth that kept the top. -/
theorem grows_snoc {m m' : Mem} (hg : Grows m m') (htop : m'.top = m.top)
    (hc : 0 < (m.arr64 CTL).size) (hcs : (m'.arr64 CTL).size = (m.arr64 CTL).size)
    (hps : (m'.arr64 POOL).size = (m.arr64 POOL).size) {q x : Word}
    (hq : m.top.toNat ≤ q.toNat) (hs : q.toNat < (m.arr64 POOL).size) :
    Grows m (m'.set64 POOL q x) ∧ (m'.set64 POOL q x).top = m.top ∧
      ((m'.set64 POOL q x).arr64 CTL).size = (m.arr64 CTL).size ∧
      ((m'.set64 POOL q x).arr64 POOL).size = (m.arr64 POOL).size := by
  have htop' : (m'.set64 POOL q x).top = m'.top := by
    simp only [top_rdW, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]
  refine ⟨Grows.trans _ _ _ hg (grows_poolSet m' q x (by omega) (by rw [htop]; exact hq) (by omega)), ?_, ?_, ?_⟩
  · rw [htop', htop]
  · rw [Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide), hcs]
  · rw [size_set64, hps]

/-- **The nine bytes and the raised top are a growth of the pool.** -/
theorem grows_ptMem (m : Mem) (hpool : PoolOK m) (hno : m.top.toNat + 9 < 2 ^ 64)
    (hs : m.top.toNat + 9 ≤ (m.arr64 POOL).size) : Grows m (ptMem m m.top) := by
  have hc := hpool.2.1
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e4 : (m.top + 4).toNat = m.top.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have e5 : (m.top + 5).toNat = m.top.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have e6 : (m.top + 6).toNat = m.top.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have e7 : (m.top + 7).toNat = m.top.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (m.top + 8).toNat = m.top.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e9 : (m.top + 9).toNat = m.top.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have s0 := grows_snoc (m := m) (Grows.refl m hpool) rfl hc rfl rfl (q := m.top) (x := 112) (by omega) (by omega)
  have s1 := grows_snoc (m := m) s0.1 s0.2.1 hc s0.2.2.1 s0.2.2.2 (q := m.top + 1) (x := 114)
    (by omega) (by omega)
  have s2 := grows_snoc (m := m) s1.1 s1.2.1 hc s1.2.2.1 s1.2.2.2 (q := m.top + 2) (x := 111)
    (by omega) (by omega)
  have s3 := grows_snoc (m := m) s2.1 s2.2.1 hc s2.2.2.1 s2.2.2.2 (q := m.top + 3) (x := 106)
    (by omega) (by omega)
  have s4 := grows_snoc (m := m) s3.1 s3.2.1 hc s3.2.2.1 s3.2.2.2 (q := m.top + 4) (x := 84)
    (by omega) (by omega)
  have s5 := grows_snoc (m := m) s4.1 s4.2.1 hc s4.2.2.1 s4.2.2.2 (q := m.top + 5) (x := 97)
    (by omega) (by omega)
  have s6 := grows_snoc (m := m) s5.1 s5.2.1 hc s5.2.2.1 s5.2.2.2 (q := m.top + 6) (x := 98)
    (by omega) (by omega)
  have s7 := grows_snoc (m := m) s6.1 s6.2.1 hc s6.2.2.1 s6.2.2.2 (q := m.top + 7) (x := 108)
    (by omega) (by omega)
  have s8 := grows_snoc (m := m) s7.1 s7.2.1 hc s7.2.2.1 s7.2.2.2 (q := m.top + 8) (x := 101)
    (by omega) (by omega)
  refine Grows.trans _ _ _ s8.1 (grows_top _ _ (by rw [s8.2.2.1]; exact hc) ?_ ?_)
  · rw [s8.2.1]; omega
  · rw [s8.2.2.2]; omega

theorem strWords_projTable : strWords "projTable" = [112, 114, 111, 106, 84, 97, 98, 108, 101] := by
  decide

/-- **The slice holds `"projTable"`.** -/
theorem ptMem_slice (m : Mem) (o : Word) (hno : o.toNat + 9 < 2 ^ 64)
    (hs : o.toNat + 9 ≤ (m.arr64 POOL).size) :
    sliceL ((ptMem m o).arr64 POOL) o.toNat 9 = strWords "projTable" := by
  have e1 : (o + 1).toNat = o.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (o + 2).toNat = o.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (o + 3).toNat = o.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e4 : (o + 4).toNat = o.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have e5 : (o + 5).toNat = o.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have e6 : (o + 6).toNat = o.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have e7 : (o + 7).toNat = o.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (o + 8).toNat = o.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  rw [strWords_projTable]
  simp only [sliceL, ptMem, ptBytes, Mem.arr64_set64_ne _ _ _ _ _ (show POOL ≠ CTL by decide),
    Mem.arr64_set64_same, Array.set!_eq_setIfInBounds, e1, e2, e3, e4, e5, e6, e7, e8,
    List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.getElem?_setIfInBounds,
    Array.size_setIfInBounds]
  simp (config := { decide := true }) [show o.toNat < (m.arr64 POOL).size by omega,
    show o.toNat + 1 < (m.arr64 POOL).size by omega, show o.toNat + 2 < (m.arr64 POOL).size by omega,
    show o.toNat + 3 < (m.arr64 POOL).size by omega, show o.toNat + 4 < (m.arr64 POOL).size by omega,
    show o.toNat + 5 < (m.arr64 POOL).size by omega, show o.toNat + 6 < (m.arr64 POOL).size by omega,
    show o.toNat + 7 < (m.arr64 POOL).size by omega, show o.toNat + 8 < (m.arr64 POOL).size by omega]

/-! ## A name handle the L check accepts is in the twin's store -/

theorem view_of_viewN_run {a a' : AState} {h : NIdx} {v : NNodeView}
    (hr : (viewN h).run a = .ok (v, a')) : a.store.lss.ls.ns.view h = some v := by
  simp only [viewN, EStore.ns, run_get_bind'] at hr
  cases e : a.store.lss.ls.ns.view h with
  | none =>
    rw [e] at hr
    simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, StateT.lift, bind,
      Except.bind] at hr
  | some w =>
    rw [e] at hr
    simp only [pure, StateT.pure, StateT.run, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
    rw [hr.1]

/-- **The L validity check of a name handle gives the twin's view.** -/
theorem name_view_isSome {m : Mem} {a : AState} (hR : ArenaR m a) (t : Word)
    (ht : ¬ 4294967295 < t) (hg : ¬ (2 : Word) < (t >>> 28))
    (hv : ¬ (((t >>> 27) &&& 1) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0))
    (hc : ¬ rdW (m.arr64 CTL) ((34 : Word) + (t >>> (28 : Word)) * (2 : Word) + ((t >>> (27 : Word)) &&& 1)) ≤
      (t &&& 134217727)) :
    (a.store.lss.ls.ns.view (decI t)).isSome = true := by
  have ht32 : t.toNat < 2 ^ 32 := by
    have := mt UInt64.lt_iff_toNat_lt.mpr ht; simp at this; omega
  have hv' : ¬ (tierW t ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0) := hv
  have hg' : (t >>> 28).toNat ≤ 2 := by
    have := mt UInt64.lt_iff_toNat_lt.mpr hg; simp at this ⊢; omega
  have cases3 : t >>> 28 = 0 ∨ t >>> 28 = 1 ∨ t >>> 28 = 2 := by
    rcases (show (t >>> 28).toNat = 0 ∨ (t >>> 28).toNat = 1 ∨ (t >>> 28).toNat = 2 by omega)
      with h | h | h
    · exact .inl (UInt64.toNat_inj.mp (by simpa using h))
    · exact .inr (.inl (UInt64.toNat_inj.mp (by simpa using h)))
    · exact .inr (.inr (UInt64.toNat_inj.mp (by simpa using h)))
  rcases cases3 with g | g | g
  · have hc' : ¬ rdW (m.arr64 CTL) (34 + tierW t) ≤ idxW t := by
      simpa [g, tierW, idxW] using hc
    rw [view_of_viewN_run (viewN_anon hR ht32 hv' g hc')]; rfl
  · have hc' : ¬ rdW (m.arr64 CTL) (36 + tierW t) ≤ idxW t := by
      have e : (34 : Word) + (1 : Word) * (2 : Word) + ((t >>> (27 : Word)) &&& 1) = 36 + tierW t := by
        have k : ∀ x : Word, (34 : Word) + (1 : Word) * (2 : Word) + x = 36 + x := fun x => by
          rw [show (34 : Word) + (1 : Word) * (2 : Word) = 36 by decide]
        exact k _
      rw [g, e] at hc; exact hc
    obtain ⟨_, hr, -⟩ := viewN_str hR ht32 hv' g hc'
    rw [view_of_viewN_run hr]; rfl
  · have hc' : ¬ rdW (m.arr64 CTL) (38 + tierW t) ≤ idxW t := by
      have e : (34 : Word) + (2 : Word) * (2 : Word) + ((t >>> (27 : Word)) &&& 1) = 38 + tierW t := by
        have k : ∀ x : Word, (34 : Word) + (2 : Word) * (2 : Word) + x = 38 + x := fun x => by
          rw [show (34 : Word) + (2 : Word) * (2 : Word) = 38 by decide]
        exact k _
      rw [g, e] at hc; exact hc
    rw [view_of_viewN_run (viewN_num hR ht32 hv' g hc').1]; rfl

/-! ## `proj_table_name` refines `projTableName` -/

/-- The run of `intern_nstr` as its word model. -/
theorem callW_nstr (p : Prog) (hp : ProjProg p) (n : Nat) (m : Mem) (q o l : Word)
    (hs : (m.arr64 POOL).size < 2 ^ 64) (hb : o.toNat + l.toNat ≤ (m.arr64 POOL).size)
    {r : List Word} {m' : Mem} (h : callW p n "intern_nstr" [q, o, l] m = some (r, m')) :
    nsinternW m q o l = some (r.headD 0, m') := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internNStr_spec p hp.litHash hp.limbsEq hp.nsMatch hp.nsFind hp.nsPush hp.nstr n _ q o l hs hb) h
  rw [← hs']; exact hW

/-- The run of `intern_nnum` as its word model. -/
theorem callW_nnum (p : Prog) (hp : ProjProg p) (n : Nat) (m : Mem) (q u : Word)
    {r : List Word} {m' : Mem} (h : callW p n "intern_nnum" [q, u] m = some (r, m')) :
    nninternW m q u = some (r.headD 0, m') := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internNNum_spec p hp.nnFind hp.nnPush hp.nnum n _ q u) h
  rw [← hs']; exact hW

theorem ptBytes_ctl (m : Mem) (o : Word) : (ptBytes m o).arr64 CTL = m.arr64 CTL := by
  simp only [ptBytes, Mem.arr64_set64_ne _ _ _ _ _ (show CTL ≠ POOL by decide)]

/-- The stack and the pool across `proj_table_name`: the bytes grow the pool, the two name
interns write the name tables only. -/
theorem ptn_kept {m m₁ m₃ : Mem} (hg : Grows m m₁)
    (hf : MemFrame [NSREC, NSSLOT, NNREC, NNSLOT] [36, 37, 38, 39] m₁ m₃) : StackKept m m₃ := by
  exact StackKept.of_frame_grows hg hf

/-- **`proj_table_name` refines `projTableName`** under `CoreS` (the result a name handle). -/
@[refines ConRon.Arena.projTableName]
theorem projTableName_refines (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb t : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe M eb) :
    CoreSpec p n "proj_table_name" [t] (projTableName (decI t)) (fun r => (decI (r.headD 0) : NIdx))
      s₀ a₀ dn vis fe M eb (fun _ => True) := by
  cases n with
  | zero => exact CoreSpec.zeroW hp.ptn _ _ _ _ _ _ _ _ _ _ _
  | succ n =>
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun (ptnW_spec p hp n s₀ t)
  subst hs0
  refine ⟨hloc, ?_⟩
  generalize hm : s.mem = m at hW hS
  unfold ptnW at hW
  by_cases c1 : 4294967295 < t
  · rw [if_pos c1] at hW; cases hW
  rw [if_neg c1] at hW
  by_cases c2 : (2 : Word) < (t >>> 28)
  · rw [if_pos c2] at hW; cases hW
  rw [if_neg c2] at hW
  by_cases c3 : ((t >>> 27) &&& 1) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [if_pos c3] at hW; cases hW
  rw [if_neg c3] at hW
  by_cases c4 : rdW (m.arr64 CTL) ((34 : Word) + (t >>> (28 : Word)) * (2 : Word) +
      ((t >>> (27 : Word)) &&& 1)) ≤ (t &&& 134217727)
  · rw [if_pos c4] at hW; cases hW
  rw [if_neg c4] at hW
  by_cases c5 : rdW (m.arr64 CTL) 0 + 9 < rdW (m.arr64 CTL) 0
  · rw [if_pos c5] at hW; cases hW
  rw [if_neg c5] at hW
  by_cases c6 : m.len64 POOL < rdW (m.arr64 CTL) 0 + 9
  · rw [if_pos c6] at hW; cases hW
  rw [if_neg c6] at hW
  have hR := hS.arena.1
  have hpool : PoolOK m := hR.lit.1
  obtain ⟨hctl, hc0, hps, htop⟩ := hpool
  generalize ho : rdW (m.arr64 CTL) 0 = o at hW c5 c6
  have hot : o = m.top := ho.symm
  have hotn : o.toNat = m.top.toNat := by rw [hot]
  have ef : (UInt64.ofNat (m.arr64 POOL).size).toNat = (m.arr64 POOL).size := by
    simp; omega
  have hno : o.toNat + 9 < 2 ^ 64 := by
    have := mt UInt64.lt_iff_toNat_lt.mpr c5
    rw [UInt64.toNat_add] at this; simp at this; omega
  have h9 : (o + 9).toNat = o.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hsz : o.toNat + 9 ≤ (m.arr64 POOL).size := by
    have := mt UInt64.lt_iff_toNat_lt.mpr c6
    rw [len64_eq, ef, h9] at this
    omega
  have hg : Grows m (ptMem m o) := by rw [hot]; exact grows_ptMem m ⟨hctl, hc0, hps, htop⟩ (by omega) (by omega)
  have hS1 : CoreS dn (ptMem m o) a₀ vis fe M eb :=
    CoreS.arena_frame hS (ArenaD.grow m _ hg a₀ hS.arena) rfl (grows_frame m _ hg)
      (by simp [POOL]) (by simp [POOL]) (by simp [POOL]) (by simp) (by simp)
  have hR1 := hS1.arena.1
  have hm1top : (ptMem m o).top = o + 9 := Mem.top_set64 _ _ (by rw [ptBytes_ctl]; exact hc0)
  have hsl : SliceOK (ptMem m o) o 9 := by
    simp only [SliceOK, hm1top, h9]; simp
  have hpsz : ((ptMem m o).arr64 POOL).size = (m.arr64 POOL).size := by
    simp only [ptMem, ptBytes, size_set64]
  have hk := ptMem_slice m o hno hsz
  cases hc1 : callW p n "intern_nstr" [t, o, 9] (ptMem m o) with
  | none => rw [hc1] at hW; cases hW
  | some q1 =>
  obtain ⟨r₁, m₂⟩ := q1
  rw [hc1] at hW
  simp only at hW
  by_cases c7 : 4294967296 ≤ r₁.headD 0
  · rw [if_pos c7] at hW; cases hW
  rw [if_neg c7] at hW
  have hW1 := callW_nstr p hp n _ t o 9 (by omega) (by rw [hpsz]; simpa using hsz) hc1
  have ht32 : t.toNat < 2 ^ 32 := by
    have := mt UInt64.lt_iff_toNat_lt.mpr c1; simp at this; omega
  have tr1 := internNStr_refinesA p hp.litHash hp.limbsEq hp.nsMatch hp.nsFind hp.nsPush hp.nstr a₀ n
      ⟨ptMem m o, Locals.init []⟩ t o 9 hR1 ht32 hsl "projTable" hk
  obtain ⟨s₂, hs₂, -, hok1, hR2, hres1⟩ := triple_of_callW tr1 hc1
  rw [hs₂] at hR2
  have hrun1 := AM.run_of_ok _ _ hok1
  have hvalid := name_view_isSome hR t c1 c2 c3 c4
  obtain ⟨hN1, hview1⟩ := internNNode_nstep hS.nwf
    (fun c hc => by simp only [NNodeView.children, List.mem_singleton] at hc; subst hc; exact hvalid)
    hrun1
  have hfr1 : MemFrame [NSREC, NSSLOT] [36, 37] (ptMem m o) m₂ := by
    exact consInternM_frame nstrCS_wf hW1
  have hS2 := CoreS.of_name hS1 hN1 hR2 hfr1 (by simp [NSREC, NSSLOT]) (by simp)
  have hr1 : (r₁.headD 0).toNat < 2 ^ 32 := by
    have := mt UInt64.le_iff_toNat_le.mpr c7
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; omega
  cases hc2 : callW p n "intern_nnum" [r₁.headD 0, 0] m₂ with
  | none => rw [hc2] at hW; cases hW
  | some q2 =>
  obtain ⟨r₂, m₃⟩ := q2
  rw [hc2] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm3⟩ := hW
  have hW2 := callW_nnum p hp n _ _ _ hc2
  have tr2 := internNNum_refinesA p hp.nnFind hp.nnPush hp.nnum
    (AM.st (internNNode (.str (decI t) "projTable")) a₀) n ⟨m₂, Locals.init []⟩ (r₁.headD 0) 0 hR2 hr1
  obtain ⟨s₃, hs₃, -, hok2, hR3, hres2⟩ := triple_of_callW tr2 hc2
  rw [hs₃] at hR3
  have hrun2 := AM.run_of_ok _ _ hok2
  rw [hres1] at hview1
  obtain ⟨hN2, -⟩ := internNNode_nstep hN1.nwf
    (fun c hc => by simp only [NNodeView.children, List.mem_singleton] at hc; subst hc; rw [hview1]; rfl)
    hrun2
  have hfr2 : MemFrame [NNREC, NNSLOT] [38, 39] m₂ m₃ := by
    exact consInternM_frame nnumCS_wf hW2
  have hS3 := CoreS.of_name hS2 hN2 hR3 hfr2 (by simp [NNREC, NNSLOT]) (by simp)
  have hrunT : (projTableName (decI t)).run a₀ =
      .ok (AM.res (internNNode (.num (decI (r₁.headD 0)) (0 : Word).toNat))
          (AM.st (internNNode (.str (decI t) "projTable")) a₀),
        AM.st (internNNode (.num (decI (r₁.headD 0)) (0 : Word).toNat))
          (AM.st (internNNode (.str (decI t) "projTable")) a₀)) := by
    have e : projTableName (decI t) = (internNNode (.str (decI t) "projTable") >>= fun s =>
        internNNode (.num s 0)) := rfl
    rw [e, StateT.run_bind, hrun1, hres1]
    exact hrun2
  obtain ⟨okT, stT, resT⟩ := AM.of_run_ok _ _ _ _ hrunT
  have hfr13 : MemFrame [NSREC, NSSLOT, NNREC, NNSLOT] [36, 37, 38, 39] (ptMem m o) m₃ :=
    (hfr1.mono (by simp) (by simp)).trans (hfr2.mono (by simp) (by simp))
  refine ⟨okT, ⟨M, ?_, KeptAll.refl M eb, ?_⟩, ?_, trivial⟩
  · rw [← hm3, stT]; exact hS3
  · rw [← hm3]; exact ptn_kept hg hfr13
  · rw [resT]; show _ = decI (r.headD 0); rw [← hr]; exact hres2

end L.Arena
