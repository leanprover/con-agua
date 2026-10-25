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
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42 ∨ (256 ≤ b ∧ b < 298)) (hC : ∀ x ∈ C, x.toNat < 42)
    (h01 : (0 : Word) ∉ C ∧ (1 : Word) ∉ C := by decide) :
    CoreS dn m' a' vis fe M eb := by
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) a hS.arena.2) hN.pers hN.scr
  refine ⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
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
          rw [← e]; exact hu) hN.lsext), hS.mode.frame hf h01.1 h01.2⟩
  · rw [hN.caches]
    exact CoreRM.frame (A := A) (C := C) (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
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
  ((((((((m.set64 (tierA 0 (o >>> 40)) (o &&& 1099511627775) 112).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 1) 114).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 2) 111).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 3) 106).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 4) 84).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 5) 97).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 6) 98).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 7) 108).set64 (tierA 0 (o >>> 40)) ((o &&& 1099511627775) + 8) 101

/-- The memory `intern_nstr` sees: the bytes, the top raised past them. -/
def ptMem (m : Mem) (o : Word) : Mem := (ptBytes m o).set64 CTL 0 (o + 9)

/-- The model of `proj_table_name`. -/
def ptnW (p : Prog) (n : Nat) (m : Mem) (t : Word) : Option (Word × Mem) :=
  if 4294967295 < t then none
  else if (2 : Word) < (t >>> 28) then none
  else if ((t >>> 27) &&& 1) ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0 then none
  else if nameCnt m (t >>> 28) ((t >>> 27) &&& 1) ≤ (t &&& 134217727) then none
  else if rdW (m.arr64 CTL) 0 + 9 < rdW (m.arr64 CTL) 0 then none
  else if m.len64 (tierA 0 (rdW (m.arr64 CTL) 0 >>> 40)) < (rdW (m.arr64 CTL) 0 &&& 1099511627775) + 9 then none
  else match callW p n "intern_nstr" [t, rdW (m.arr64 CTL) 0, 9] (ptMem m (rdW (m.arr64 CTL) 0)) with
    | none => none
    | some (r₁, m₁) =>
      if 4294967296 ≤ r₁.headD 0 then none
      else match callW p n "intern_nnum" [r₁.headD 0, 0] m₁ with
        | none => none
        | some (r₂, m₂) => some (r₂.headD 0, m₂)

set_option maxHeartbeats 2000000 in
theorem ptnW_spec (p : Prog) (hp : ProjProg p) (n : Nat) (s₀ : St) (t : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "proj_table_name" [t]
    ⦃fun r s' => LocEq s' s₀ ∧ ptnW p n s₀.mem t = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp.ptn]
  simp only [callFn, projTableNameL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, st64, evalE_tierE, evalE_idxE,
      callW_spec p n "intern_nstr", callW_spec p n "intern_nnum"] <;>
    finish [ptnW, ptMem, ptBytes, tierW, idxW, nameCnt]

/-! ## The pool bytes -/

/-- A writer's store `POOL⟨⦃T⦄.tier⟩[⦃T⦄.idx + k] := v` inside the tier's array, as a store into
the virtual pool. -/
theorem vpool_st_k (X : Mem) (T k v : Word) (h41 : T.toNat < 2 ^ 41)
    (hsz : (X.arr64 (tierA 0 (T >>> 40))).size ≤ 2 ^ 40)
    (hk : (T &&& 1099511627775).toNat + k.toNat < (X.arr64 (tierA 0 (T >>> 40))).size) :
    vpool (X.set64 (tierA 0 (T >>> 40)) ((T &&& 1099511627775) + k) v) = (vpool X).set! (T + k).toNat v :=
  vpool_stidx X T k v h41 (by rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]; omega) hsz (by omega)

theorem ptBytes_vpool (m : Mem) (h41 : m.top.toNat < 2 ^ 41)
    (hsz : (m.arr64 (tierA 0 (m.top >>> 40))).size ≤ 2 ^ 40)
    (hk : (m.top &&& 1099511627775).toNat + 9 ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size) :
    vpool (ptBytes m m.top) = (((((((((vpool m).set! m.top.toNat 112).set! (m.top + 1).toNat 114).set! (m.top + 2).toNat 111).set! (m.top + 3).toNat 106).set! (m.top + 4).toNat 84).set! (m.top + 5).toNat 97).set! (m.top + 6).toNat 98).set! (m.top + 7).toNat 108).set! (m.top + 8).toNat 101 := by
  simp only [ptBytes]
  repeat rw [vpool_st_k _ _ _ _ h41 (by simp only [Mem.size_arr64_set64]; omega)
    (by simp only [Mem.size_arr64_set64, UInt64.reduceToNat]; omega)]
  rw [vpool_stidx0 _ _ _ h41 (by omega) (by omega)]

theorem ptBytes_frame (m : Mem) (o : Word) : PFrame m (ptBytes m o) := by
  simp only [ptBytes]
  repeat apply PFrame.set64
  exact PFrame.refl _

theorem strWords_projTable : strWords "projTable" = [112, 114, 111, 106, 84, 97, 98, 108, 101] := by
  decide

/-- **`proj_table_name`'s pool bytes**: past its length check, the nine bytes and the raised top
grow the pool and hold `"projTable"` at the old top. -/
theorem ptMem_facts (m : Mem) (hpool : PoolOK m)
    (h : ¬ m.len64 (tierA 0 (m.top >>> 40)) < (m.top &&& 1099511627775) + 9) :
    Grows m (ptMem m m.top) ∧ SliceOK (ptMem m m.top) m.top 9 ∧
      sliceL (vpool (ptMem m m.top)) m.top.toNat 9 = strWords "projTable" := by
  have hsm := hpool.small
  have h41 := hpool.top41
  have hsz := hsm.tier (m.top >>> 40)
  have hil := tag_idx_lt m.top
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hi9 : ((m.top &&& 1099511627775) + 9).toNat = (m.top &&& 1099511627775).toNat + 9 := by
    have : (9 : Word).toNat = 9 := rfl
    rw [UInt64.toNat_add, this, Nat.mod_eq_of_lt (by omega)]
  have hk : (m.top &&& 1099511627775).toNat + 9 ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp h)
    rw [hlen, hi9] at this; exact this
  have b0 : m.top.toNat < 2199023255552 := by omega
  have b1 : m.top.toNat + 1 < 2199023255552 := by omega
  have b2 : m.top.toNat + 2 < 2199023255552 := by omega
  have b3 : m.top.toNat + 3 < 2199023255552 := by omega
  have b4 : m.top.toNat + 4 < 2199023255552 := by omega
  have b5 : m.top.toNat + 5 < 2199023255552 := by omega
  have b6 : m.top.toNat + 6 < 2199023255552 := by omega
  have b7 : m.top.toNat + 7 < 2199023255552 := by omega
  have b8 : m.top.toNat + 8 < 2199023255552 := by omega
  have hv := ptBytes_vpool m h41 (by omega) hk
  have e1 : (m.top + 1).toNat = m.top.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have e2 : (m.top + 2).toNat = m.top.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have e3 : (m.top + 3).toNat = m.top.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  have e4 : (m.top + 4).toNat = m.top.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have e5 : (m.top + 5).toNat = m.top.toNat + 5 := by rw [UInt64.toNat_add]; simp; omega
  have e6 : (m.top + 6).toNat = m.top.toNat + 6 := by rw [UInt64.toNat_add]; simp; omega
  have e7 : (m.top + 7).toNat = m.top.toNat + 7 := by rw [UInt64.toNat_add]; simp; omega
  have e8 : (m.top + 8).toNat = m.top.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  have e9 : (m.top + 9).toNat = m.top.toNat + 9 := by rw [UInt64.toNat_add]; simp; omega
  have hg : Grows m (ptMem m m.top) :=
    Grows.write m _ 9 hpool (ptBytes_frame m m.top) (by
      rw [hv]
      repeat refine Agree.set _ _ _ _ _ ?_ (by omega)
      exact Agree.refl _ _) (by simp only [UInt64.reduceToNat]; omega)
  have hctl : 0 < ((ptBytes m m.top).arr64 CTL).size := by rw [(ptBytes_frame m m.top).ctl]; exact hpool.2.1
  refine ⟨hg, SliceOK.fresh hg (Mem.top_set64 _ _ hctl), ?_⟩
  rw [ptMem, vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, hv, strWords_projTable]
  simp only [sliceL, List.ofFn_succ, List.ofFn_zero, Fin.val_zero, Fin.val_succ, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, Array.size_setIfInBounds, vpool_size, e1, e2, e3, e4, e5, e6, e7, e8]
  simp (config := { decide := true }) [b0, b1, b2, b3, b4, b5, b6, b7, b8]

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
    (hc : ¬ nameCnt m (t >>> 28) ((t >>> 27) &&& 1) ≤
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
  · have hc' : ¬ tcnt m NANON (tierW t) ≤ idxW t := by
      simpa [g, tierW, idxW, nameCnt] using hc
    rw [view_of_viewN_run (viewN_anon hR ht32 hv' g hc')]; rfl
  · have hc' : ¬ tcnt m NSTR (tierW t) ≤ idxW t := by
      simpa [g, tierW, idxW, nameCnt] using hc
    obtain ⟨_, hr, -⟩ := viewN_str hR ht32 hv' g hc'
    rw [view_of_viewN_run hr]; rfl
  · have hc' : ¬ tcnt m NNUM (tierW t) ≤ idxW t := by
      simpa [g, tierW, idxW, nameCnt] using hc
    rw [view_of_viewN_run (viewN_num hR ht32 hv' g hc').1]; rfl

/-! ## `proj_table_name` refines `projTableName` -/

/-- The run of `intern_nstr` as its word model. -/
theorem callW_nstr (p : Prog) (hp : ProjProg p) (n : Nat) (m : Mem) (q o l : Word)
    (hs : pcap m < 2 ^ 64) (hb : o.toNat + l.toNat ≤ pcap m)
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

theorem ptBytes_ctl (m : Mem) (o : Word) : (ptBytes m o).arr64 CTL = m.arr64 CTL :=
  (ptBytes_frame m o).ctl

/-- The stack and the pool across `proj_table_name`: the bytes grow the pool, the two name
interns write the name tables only. -/
theorem ptn_kept {m m₁ m₃ : Mem} (hg : Grows m m₁)
    (hf : MemFrame [NSREC, NSREC + 256, NSSLOT, NSSLOT + 256, NNREC, NNREC + 256, NNSLOT, NNSLOT + 256] [36, 37, 38, 39] m₁ m₃) : StackKept m m₃ := by
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
  refine triple_post (ptnW_spec p hp n s₀ t) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  generalize hm : s₀.mem = m at hW hS
  unfold ptnW at hW
  obtain ⟨c1, hW⟩ := of_ite_none hW
  obtain ⟨c2, hW⟩ := of_ite_none hW
  obtain ⟨c3, hW⟩ := of_ite_none hW
  by_cases c4 : nameCnt m (t >>> 28) ((t >>> 27) &&& 1) ≤ (t &&& 134217727)
  · rw [if_pos c4] at hW; cases hW
  rw [if_neg c4] at hW
  obtain ⟨c5, hW⟩ := of_ite_none hW
  obtain ⟨c6, hW⟩ := of_ite_none hW
  have hR := hS.arena.1
  have hpool : PoolOK m := hR.lit.1
  generalize ho : rdW (m.arr64 CTL) 0 = o at hW c5 c6
  have hot : o = m.top := ho.symm
  subst hot
  obtain ⟨hg, hsl, hkv⟩ := ptMem_facts m hpool c6
  have hS1 : CoreS dn (ptMem m m.top) a₀ vis fe M eb :=
    CoreS.arena_frame hS (ArenaD.grow m _ hg a₀ hS.arena) rfl (grows_frame m _ hg)
      (by simp [POOL, POOL1]) (by simp [POOL, POOL1]) (by simp [POOL, POOL1]) (by simp) (by simp)
  have hR1 := hS1.arena.1
  have hcap : m.top.toNat + 9 ≤ pcap (ptMem m m.top) := by
    have := hsl.le; have := hg.cap; simp only [UInt64.reduceToNat] at *; omega
  have hpc : pcap (ptMem m m.top) < 2 ^ 64 := by rw [hg.pcapEq]; have := hpool.2.2.1; omega
  rcases hc1 : callW p n "intern_nstr" [t, m.top, 9] (ptMem m m.top) with _ | ⟨r₁, m₂⟩ <;>
    simp only [hc1, reduceCtorEq] at hW
  obtain ⟨c7, hW⟩ := of_ite_none hW
  have hW1 := callW_nstr p hp n _ t m.top 9 hpc (by simpa using hcap) hc1
  have ht32 : t.toNat < 2 ^ 32 := by
    have := mt UInt64.lt_iff_toNat_lt.mpr c1; simp at this; omega
  have tr1 := internNStr_refinesA p hp.litHash hp.limbsEq hp.nsMatch hp.nsFind hp.nsPush hp.nstr a₀ n
      ⟨ptMem m m.top, Locals.init []⟩ t m.top 9 hR1 ht32 hsl "projTable" hkv
  obtain ⟨s₂, hs₂, -, hok1, hR2, hres1⟩ := triple_of_callW (tr1 (ModeOK.slice0 hS1.mode hsl)) hc1
  rw [hs₂] at hR2
  have hrun1 := AM.run_of_ok _ _ hok1
  have hvalid := name_view_isSome hR t c1 c2 c3 c4
  obtain ⟨hN1, hview1⟩ := internNNode_nstep hS.nwf
    (fun c hc => by simp only [NNodeView.children, List.mem_singleton] at hc; subst hc; exact hvalid)
    hrun1
  have hfr1 : MemFrame [NSREC, NSREC + 256, NSSLOT, NSSLOT + 256] [36, 37] (ptMem m m.top) m₂ :=
    (consInternM_frame nstrCS_wf hW1).mono (by simp [ConsSch.wset, nstrCS, nstrSch])
      (by simp [nstrCS, nstrSch])
  have hS2 := CoreS.of_name hS1 hN1 hR2 hfr1 (by decide) (by simp)
  have hr1 : (r₁.headD 0).toNat < 2 ^ 32 := by
    have := mt UInt64.le_iff_toNat_le.mpr c7
    have e : (4294967296 : Word).toNat = 4294967296 := rfl
    rw [e] at this; omega
  rcases hc2 : callW p n "intern_nnum" [r₁.headD 0, 0] m₂ with _ | ⟨r₂, m₃⟩ <;>
    simp only [hc2, reduceCtorEq] at hW
  obtain ⟨hr, hm3⟩ := Prod.mk.inj (Option.some.inj hW)
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
  have hfr2 : MemFrame [NNREC, NNREC + 256, NNSLOT, NNSLOT + 256] [38, 39] m₂ m₃ :=
    (consInternM_frame nnumCS_wf hW2).mono (by simp [ConsSch.wset, nnumCS, nnumSch])
      (by simp [nnumCS, nnumSch])
  have hS3 := CoreS.of_name hS2 hN2 hR3 hfr2 (by decide) (by simp)
  have hrunT : (projTableName (decI t)).run a₀ =
      .ok (AM.res (internNNode (.num (decI (r₁.headD 0)) (0 : Word).toNat))
          (AM.st (internNNode (.str (decI t) "projTable")) a₀),
        AM.st (internNNode (.num (decI (r₁.headD 0)) (0 : Word).toNat))
          (AM.st (internNNode (.str (decI t) "projTable")) a₀)) := by
    have e : projTableName (decI t) = (internNNode (.str (decI t) "projTable") >>= fun s₀ =>
        internNNode (.num s₀ 0)) := rfl
    rw [e, StateT.run_bind, hrun1, hres1]
    exact hrun2
  obtain ⟨okT, stT, resT⟩ := AM.of_run_ok _ _ _ _ hrunT
  have hfr13 : MemFrame [NSREC, NSREC + 256, NSSLOT, NSSLOT + 256, NNREC, NNREC + 256, NNSLOT, NNSLOT + 256] [36, 37, 38, 39] (ptMem m m.top) m₃ :=
    (hfr1.mono (by simp) (by simp)).trans (hfr2.mono (by simp) (by simp))
  refine ⟨okT, ⟨M, ?_, KeptAll.refl M eb, ?_⟩, ?_, trivial⟩
  · rw [← hm3, stT]; exact hS3
  · rw [← hm3]; exact ptn_kept hg hfr13
  · rw [resT]; show _ = decI (r.headD 0); rw [← hr]; exact hres2

end L.Arena
