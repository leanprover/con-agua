import ConAgua.Arena.StrLit
import ConAgua.Arena.DefEqStuckEta
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.InferFieldSortNat
import ConAgua.Arena.RomExpr

/-!
# The string-literal functions' leaves under `CoreS` (helper `defeq2-str`)

Every callee of `StrLit.lean`'s functions as a `callW` run under `CoreS`, in the shape
`CoreRef T a dec …` (the twin's run, the relation after it, the result decoded), so that a
caller's refinement chains them with `coreRef_bind`:

* the level nodes `intern_param`, `intern_zero` (as `internSucc_core`, `InferBodyIntern.lean`);
* the one-element level list `str_ls1(u)`: the pool push, then `intern_ls`; `CoreS.of_ls` is
  `CoreS` across a level-list interning (the list tables only grow: `LsStore.view_intern_mono`);
* the expression nodes `intern_bvar`, `intern_const`, `const_e`, `mk_app`, `intern_sort`, and a
  character's literal `rom_lit(c)`.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace L.Arena

/-! ## A level-list interning step -/

/-- **What a level-list interning keeps**: everything but the list tables, which only grow. -/
structure LsStep (a a' : AState) : Prop where
  caches : a'.caches = a.caches
  pins : a'.pins = a.pins
  pers : a'.store.pers = a.store.pers
  scr : a'.store.scr = a.store.scr
  ls : a'.store.lss.ls = a.store.lss.ls
  view : ∀ i v, a.store.lss.view i = some v → a'.store.lss.view i = some v
  son : a'.store.scratchOn = a.store.scratchOn

theorem internLsNode_step (v : LsNodeView) (a a' : AState) (h : LsIdx)
    (hrun : (internLsNode v).run a = .ok (h, a')) : LsStep a a' := by
  unfold internLsNode at hrun
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrun
  repeat' split at hrun
  all_goals simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
    StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure] at hrun
  all_goals first
    | (obtain ⟨-, rfl⟩ := hrun; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ h => h, rfl⟩)
    | (obtain ⟨-, rfl⟩ := hrun
       exact ⟨rfl, rfl, rfl, rfl, LsStore.ls_intern _ _,
         fun _ _ h => LsStore.view_intern_mono _ _ h, rfl⟩)

/-- **`CoreS` across a level-list interning** whose memory writes are confined to the level
stores' arrays (below 42) and counts (`CTL` below 42). -/
theorem CoreS.of_ls {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hL : LsStep a a') (hR : ArenaR m' a')
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42 ∨ (54 < b ∧ b < 64) ∨ (256 ≤ b ∧ b < 298) ∨ (310 < b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 42)
    (hlsa : LsAll a') (hlc : LvlCnt m m')
    (hP : POOL ∉ A := by decide) (hP0 : (0 : Word) ∉ C := by decide) (hP1 : POOL1 ∉ A := by decide)
    (hPT : PT0 ∉ A := by decide) :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  have hmode : ModeOK m' := by
    have hfl : m'.flag = m.flag := hlc.flag
    unfold ModeOK; rw [hf.top_eq hP0, hfl]; exact hS.mode
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega) a
      hS.arena.2) hL.pers hL.scr
  refine ⟨⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => .inl (by have := hC x hx; omega)) hf
      (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega), ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
      hS.memos.frame hf ⟨fun h => absurd (hA _ h) (by simp), fun h => absurd (hA _ h) (by simp)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by simp), fun h => absurd (hA _ h) (by simp),
          fun h => absurd (hA _ h) (by simp)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by simp), fun h => absurd (hA _ h) (by simp),
          fun h => absurd (hA _ h) (by simp)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩,
      hf.2.2.1 145 ▸ hS.bstk,
      hS.den.mono ⟨by rw [hL.ls]; exact LExt.refl _, fun i us h => by
          unfold denoteLs at h ⊢
          revert h
          cases e : a.store.lss.view i with
          | none => intro h; cases h
          | some v => intro h; rw [hL.view i v e, hL.ls]; exact h⟩
        (by rw [hL.pins]) (by rw [hL.pins]) (fun _ _ hk => .inl (hL.caches ▸ hk))
        (fun x u hv => by simpa only [EStore.view, hL.pers, hL.scr, hL.son] using hv)
        (fun x c us hv => .inl (by simpa only [EStore.view, hL.pers, hL.scr, hL.son] using hv))
        (hS.den.lvlAll.congr (by simp only [EStore.ls, hL.ls])) hlsa, hmode⟩,
    StackKept.of_frameL hf
      ⟨fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega,
       fun h => by have := hA _ h; simp only [BSTK, ArrId] at this; omega, hP⟩
      ⟨fun h => by have := hC _ h; simp at this, fun h => by have := hC _ h; simp at this, hP0⟩ hlc hP1 hPT⟩
  · rw [hL.caches]
    exact CoreRM.frame (A := A) (C := C) (fun b hb => by have := hA b hb; simp only [ArrId] at this ⊢; omega)
      (fun x hx => .inl (by have := hC x hx; omega)) hf hS.core
  · rw [hL.pins]
    exact hS.pins.congr (hf.1 PINS (fun h => by have := hA _ h; simp only [PINS, ArrId] at this; omega)
      (by decide))
  · intro h l e
    rw [hL.caches] at e
    have := hS.readL h l e
    simp only [EStore.ls] at this ⊢
    rw [hL.ls]; exact this
  · intro h l e
    rw [hL.caches] at e
    have h1 := hS.readLs h l e
    unfold denoteLs at h1 ⊢
    cases hw : a.store.lss.view h with
    | none => rw [hw] at h1; cases h1
    | some us =>
      rw [hw] at h1
      rw [hL.view h us hw, hL.ls]; exact h1
  · rw [hL.ls]; exact hS.nwf

/-! ## The program -/

/-- What the string-literal specs need of a program: `StrLit.lean`'s functions and the callees'. -/
structure StrLitProg (p : Prog) : Prop extends WhnfDeltaProg' p where
  strCv : p.lookup "str_cv" = some strCvL
  stringTyOk : p.lookup "string_ty_ok" = some stringTyOkL
  charTyOk : p.lookup "char_ty_ok" = some charTyOkL
  strParamSort : p.lookup "str_param_sort" = some strParamSortL
  strLs1 : p.lookup "str_ls1" = some strLs1L
  listTyOk : p.lookup "list_ty_ok" = some listTyOkL
  listNilTyOk : p.lookup "list_nil_ty_ok" = some listNilTyOkL
  listConsTyOk : p.lookup "list_cons_ty_ok" = some listConsTyOkL
  charOfNatTyOk : p.lookup "char_of_nat_ty_ok" = some charOfNatTyOkL
  stringOfListTyOk : p.lookup "string_of_list_ty_ok" = some stringOfListTyOkL
  strSup7 : p.lookup "str_sup_7" = some strSup7L
  strSup6 : p.lookup "str_sup_6" = some strSup6L
  strSup5 : p.lookup "str_sup_5" = some strSup5L
  strSup4 : p.lookup "str_sup_4" = some strSup4L
  strSup3 : p.lookup "str_sup_3" = some strSup3L
  strSup2 : p.lookup "str_sup_2" = some strSup2L
  strSup1 : p.lookup "str_sup_1" = some strSup1L
  strLitSupported : p.lookup "str_lit_supported" = some strLitSupportedL
  strUtf8Char : p.lookup "str_utf8_char" = some strUtf8CharL
  strConsSpine : p.lookup "str_cons_spine" = some strConsSpineL
  strLitCtor : p.lookup "str_lit_ctor" = some strLitCtorL
  strCtorPre : p.lookup "str_ctor_pre" = some strCtorPreL
  paramFind : p.lookup "param_find" = some paramFind
  paramPush : p.lookup "param_push" = some paramPush
  internParam : p.lookup "intern_param" = some internParam
  succFind : p.lookup "succ_find" = some succFind
  succPush : p.lookup "succ_push" = some succPush
  internSucc : p.lookup "intern_succ" = some internSucc
  zeroFind : p.lookup "zero_find" = some zeroFind
  zeroPush : p.lookup "zero_push" = some zeroPush
  internZero : p.lookup "intern_zero" = some internZero
  sortFind : p.lookup "sort_find" = some sortFind
  sortPush : p.lookup "sort_push" = some sortPush
  internSort : p.lookup "intern_sort" = some internSort
  bvarFind : p.lookup "bvar_find" = some bvarFind
  bvarPush : p.lookup "bvar_push" = some bvarPush
  internBVar : p.lookup "intern_bvar" = some internBVar
  lsMatch : p.lookup "ls_match" = some lsMatch
  lsFind : p.lookup "ls_find" = some lsFind
  lsPush : p.lookup "ls_push" = some lsPush
  internLs : p.lookup "intern_ls" = some internLs
  eView : p.lookup "e_view" = some L.Ind.eView
  romLit : p.lookup "rom_lit" = some L.Rom.romLit

/-! ## The level leaves -/

section leaves
variable {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word}
  {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- **`intern_param` refines `internLNode (.param …)` under `CoreS`.** -/
theorem internParam_core (hS : CoreS dn m a vis fe M eb) (u : Word) (hu : HW u)
    (rs : List Word) (hI : pinternW m u = some (rs.headD 0, m'))
    (hdn : ∃ x, denoteN a.store.ls.ns (decI u) = some x) :
    CoreRef (internLNode (.param (decI u))) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hS.arena.1.param u hu _ _ hI
  have hLp := pintern_hp m a hS.arena.1.param u hu hS.arena.1.paramHp _ _ hI
  have hI₂ := hI
  have hf := consInternM_frame paramCS_wf hI₂
  have hR' := hS.arena.1.lift_param _ _ _ _ ⟨hX, hLp⟩ hf
    (AM.st_proto paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [ConsSch.wset, paramCS, paramSch, Option.toList, List.map_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [paramCS, paramSch, Option.toList, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (lvlAll_internLNode hS.arena.1 hS.den.lvlAll
      (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn => by
        simp only [LNodeView.nchildren, List.mem_cons, List.mem_nil_iff, or_false] at hn
        subst hn; exact hdn) (AM.run_of_ok _ _ hok)).1
    (lvlCnt_of_arena hS.arena.1 hR' (hf.2.1 1 (by decide))
      (LTGrow.internLNode (AM.run_of_ok _ _ hok)).1 (LTGrow.internLNode (AM.run_of_ok _ _ hok)).2
      (by simp [hL.lsp]) (by simp [hL.lss]))
  have hw := consInternM_lt paramCS_wf hS.arena.1.param hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_zero` refines `internLNode .zero` under `CoreS`.** -/
theorem internZero_core (hS : CoreS dn m a vis fe M eb)
    (rs : List Word) (hI : zinternW m = some (rs.headD 0, m')) :
    CoreRef (internLNode .zero) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := zintern_correct m a hS.arena.1.zero _ _ hI
  have hLp := zintern_hp m a hS.arena.1.zero hS.arena.1.zeroHp _ _ hI
  have hI₂ := hI
  have hf := consInternM_frame zeroCS_wf hI₂
  have hR' := hS.arena.1.lift_zero _ _ _ _ ⟨hX, hLp⟩ hf
    (AM.st_proto zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [ConsSch.wset, zeroCS, zeroSch, Option.toList, List.map_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [zeroCS, zeroSch, Option.toList, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (lvlAll_internLNode hS.arena.1 hS.den.lvlAll
      (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn => by simp [LNodeView.nchildren] at hn) (AM.run_of_ok _ _ hok)).1
    (lvlCnt_of_arena hS.arena.1 hR' (hf.2.1 1 (by decide))
      (LTGrow.internLNode (AM.run_of_ok _ _ hok)).1 (LTGrow.internLNode (AM.run_of_ok _ _ hok)).2
      (by simp [hL.lsp]) (by simp [hL.lss]))
  have hw := consInternM_lt zeroCS_wf hS.arena.1.zero hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

end leaves

/-! ## A `lit` interning under `CoreS` -/

section litc
variable {dn : NIdx → Option ConLeche.Name} {m m₀ m' : Mem} {a : AState} {vis : Word}
  {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- **`internW` under `CoreK`**: the twin's `lit` interning of the slice's value. -/
theorem internW_core (hK : CoreK dn vis fe M eb m₀ m a) (o l : Word) (hq : SliceOK m o l)
    (hn : Norm (vpool m) o.toNat l.toNat) (w : Word) (hI : internW m o l = some (w, m')) :
    CoreRef (internE (.lit (.natVal (pv (vpool m) o.toNat l.toNat)))) a
      decH dn m₀ vis fe M eb [w] m' := by
  obtain ⟨hok, hD, hres⟩ := internLit_D m a hK.1.arena o l _ hq hn (ModeOK.slice0 hK.1.mode hq) _ hI
  have hI₂ := hI
  have hfr := consInternM_frame litCS_wf hI₂
  simp only [ConsSch.wset, litCS, litCSk, litSch, Option.toList, List.map_nil, List.append_nil] at hfr
  have hcpl := (keeps_cpl_internLit (.natVal (pv (vpool m) o.toNat l.toNat))).run
    (AM.run_of_ok _ _ hok)
  refine ⟨hok, ⟨M, hK.1.arena_frame hD hcpl hfr ?_ ?_ ?_ ?_ ?_,
    KeptAll.refl _ _, hK.2.trans (StackKept.of_frame hfr)⟩,
    hres, internW_hw m a hK.1.arena.1.lit o l w m' hI⟩
  · intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  · simp [REC, SLOT, PINS]
  · intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl <;> decide
  · intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> decide

/-- **`rom_lit(c)`'s model under `CoreS`**: the twin's `Nat` literal `c`. -/
theorem romLitW_core (hS : CoreS dn m a vis fe M eb) (c w : Word) (hI : L.Rom.romLitW m c = some (w, m')) :
    CoreRef (internE (.lit (.natVal c.toNat))) a decH dn m vis fe M eb [w] m' := by
  have hpool : PoolOK m := hS.arena.1.lit.1
  unfold L.Rom.romLitW at hI
  by_cases hlen : m.len64 (tierA 0 (m.top >>> 40)) ≤ (m.top &&& 1099511627775)
  · rw [if_pos hlen] at hI; cases hI
  rw [if_neg hlen] at hI
  by_cases hc : c = 0
  · rw [if_pos hc] at hI
    have h := internW_core (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
      ⟨hS, StackKept.refl _⟩ m.top 0 ⟨by simp, by omega⟩ (by simp [Norm]) w hI
    subst hc
    simpa [pv] using h
  · rw [if_neg hc] at hI
    obtain ⟨hg, hq, hpwv⟩ := L.Rom.litWordMem_facts m c hpool hlen
    have hK := CoreK.grow (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
      ⟨hS, StackKept.refl _⟩ hg
    have h := internW_core hK m.top 1 hq (by intro _; simp [hpwv, hc]) w hI
    have hv : pv (vpool (L.Rom.litWordMem m c)) m.top.toNat (1 : Word).toNat = c.toNat := by
      simp [pv, wt, hpwv]
    rw [hv] at h; exact h

end litc

/-! ## `str_ls1` -/

/-- The model of `str_ls1`: the handle `u` at the pool top (in the top's tier, relative to its
base), the top moved past it, then `intern_ls(top, 1)`. -/
def ls1W (p : Prog) (n : Nat) (m : Mem) (u : Word) : Option (Word × Mem) :=
  if m.len64 (tierA 0 (m.top >>> 40)) ≤ m.top - (m.top >>> 40) <<< 40 then none
  else match callW p n "intern_ls" [m.top, 1]
      ((m.set64 (tierA 0 (m.top >>> 40)) (m.top - (m.top >>> 40) <<< 40) u).set64 CTL 0 (m.top + 1)) with
    | none => none
    | some (r, m') => some (r.headD 0, m')

/-- `x - base(x)` is `x`'s index in its tier. -/
theorem tag_sub_base' (x : Word) : x - (x >>> 40) <<< 40 = x &&& 1099511627775 := by
  apply UInt64.toNat_inj.mp; rw [tag_off_toNat, tag_idx_toNat]

/-- **A one-word push at the top** (`POOL⟨⦃top⦄.tier⟩[top - ⦃top⦄.base] := v; CTL[0] := top + 1`,
inside the top's tier array): the pool grew, and the new word is `v`. -/
theorem Grows.push1t (m : Mem) (v : Word) (h : PoolOK m)
    (hs : ¬ m.len64 (tierA 0 (m.top >>> 40)) ≤ m.top - (m.top >>> 40) <<< 40) :
    Grows m ((m.set64 (tierA 0 (m.top >>> 40)) (m.top - (m.top >>> 40) <<< 40) v).set64 CTL 0
      (m.top + 1)) ∧
    (vpool ((m.set64 (tierA 0 (m.top >>> 40)) (m.top - (m.top >>> 40) <<< 40) v).set64 CTL 0
      (m.top + 1)))[m.top.toNat]? = some v ∧
    ((m.set64 (tierA 0 (m.top >>> 40)) (m.top - (m.top >>> 40) <<< 40) v).set64 CTL 0
      (m.top + 1)).top = m.top + 1 := by
  have h41 := h.top41
  have hsz := h.small.tier (m.top >>> 40)
  rw [tag_sub_base'] at hs ⊢
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)
  have hlt : (m.top &&& 1099511627775).toNat < (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    rw [UInt64.not_le, UInt64.lt_iff_toNat_lt, hlen] at hs; exact hs
  have hv := vpool_stidx0 m m.top v h41 hlt (by omega)
  have hg := Grows.write m _ 1 h (PFrame.set64 _ _ _ (PFrame.refl _))
    (by rw [hv]; intro j hj; rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
      if_neg (by omega)]) (by simp only [UInt64.toNat_one]; omega)
  refine ⟨hg, ?_, Mem.top_set64 _ _ (by rw [arr64_set64_tier_ne _ _ _ _ _ (by decide)]; exact h.2.1)⟩
  rw [vpool_set64_ne _ _ _ _ (by decide), hv, Array.set!_eq_setIfInBounds,
    Array.getElem?_setIfInBounds, if_pos rfl, if_pos (by rw [vpool_size]; exact h41)]

theorem strLs1_spec (p : Prog) (hp : p.lookup "str_ls1" = some strLs1L) (n : Nat) (s₀ : St)
    (u : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "str_ls1" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ ls1W p n s₀.mem u = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, strLs1L]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      callW_spec p n "intern_ls"] <;>
    finish [ls1W, Mem.top]

/-! ## The callees as runs under `CoreS` -/

section calls
variable (p : Prog) (hp : StrLitProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem}
  {a : AState} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word}
include hp

theorem param_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "intern_param" [u] m = some (r, m'))
    (hdn : ∃ x, denoteN a.store.ls.ns (decI u) = some x) :
    CoreRef (internLNode (.param (decI u))) a decLv dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internParam_spec p hp.paramFind hp.paramPush hp.internParam n _ u) h
  rw [hs'] at hI
  exact internParam_core hS u hu r hI hdn

theorem succ_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "intern_succ" [u] m = some (r, m'))
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) :
    CoreRef (internLNode (.succ (decI u))) a decLv dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSucc_spec p hp.succFind hp.succPush hp.internSucc n _ u) h
  rw [hs'] at hI
  exact internSucc_core hS u hu r hI hdu

theorem zero_call (hS : CoreS dn m a vis fe M eb)
    (h : callW p n "intern_zero" [] m = some (r, m')) :
    CoreRef (internLNode .zero) a decLv dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internZero_spec p hp.zeroFind hp.zeroPush hp.internZero n _) h
  rw [hs'] at hI
  exact internZero_core hS r hI

theorem sort_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "intern_sort" [u] m = some (r, m'))
    (hdu : ∃ l, denoteL a.store.ls (decI u) = some l) :
    CoreRef (internE (.sort (decI u))) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSort_spec p hp.sortFind hp.sortPush hp.internSort n _ u) h
  rw [hs'] at hI
  exact internSort_core hS u hu r hI hdu

theorem bvar_call (hS : CoreS dn m a vis fe M eb) {u : Word}
    (h : callW p n "intern_bvar" [u] m = some (r, m')) :
    CoreRef (internE (.bvar u.toNat)) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internBVar_spec p hp.bvarFind hp.bvarPush hp.internBVar n _ u) h
  rw [hs'] at hI
  obtain ⟨hok, hD, hres⟩ := internBVar_D m a hS.arena u _ _ hI
  have hfr := binternW_frame _ _ _ _ hI
  exact ⟨hok, ⟨M, hS.of_bvar hD (Keeps.run (keeps_cpl_internBVar _) (AM.run_of_ok _ _ hok)) hfr,
    KeptAll.refl _ _, StackKept.of_bvar_frame hfr⟩, by rw [hres]; rfl,
    binternW_hw _ a hS.arena.1.bvar _ _ _ hI⟩

theorem const_call (hS : CoreS dn m a vis fe M eb) {f x : Word} (hf : HW f) (hx : HW x)
    (h : callW p n "intern_const" [f, x] m = some (r, m'))
    (hus : ∃ ls, denoteLs a.store.lss (decI x) = some ls) :
    CoreRef (internE (.const (decI f) (decI x))) a decH dn m vis fe M eb r m' := by
  obtain ⟨hok, hD, hres, hfr, hhw⟩ := callW_internConst p hp.constFind' hp.constPush' hp.internConst
    n ⟨m, Locals.init []⟩ a hS.arena f x hf hx r m' h
  exact ⟨hok, ⟨M, hS.of_const hD (Keeps.run (keeps_cpl_internConst _ _) (AM.run_of_ok _ _ hok)) hfr
    (AM.run_of_ok _ _ hok) hus, KeptAll.refl _ _, StackKept.of_const_frame hfr⟩, hres, hhw⟩

theorem constE_call (hS : CoreS dn m a vis fe M eb) {x : Word} (hx : HW x)
    (h : callW p n "const_e" [x] m = some (r, m')) :
    CoreRef (constE (decI x)) a decH dn m vis fe M eb r m' := by
  obtain ⟨hok, hS', hres, hfr, hhw⟩ := callW_constE p hp.toWhnfDeltaProg' n ⟨m, Locals.init []⟩ a dn
    vis fe M eb x hS hx r m' h
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, StackKept.of_const_frame hfr⟩, hres, hhw⟩

theorem app_call (hS : CoreS dn m a vis fe M eb) {f x : Word}
    (h : callW p n "mk_app" [f, x] m = some (r, m')) :
    CoreRef (internE (.app (decE f) (decE x))) a decH dn m vis fe M eb r m' :=
  mkApp_core hp.spine hS f x r h

theorem romLit_call (hS : CoreS dn m a vis fe M eb) {c : Word}
    (h : callW p n "rom_lit" [c] m = some (r, m')) :
    CoreRef (internE (.lit (.natVal c.toNat))) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Rom.romLit_spec p hp.litHash' hp.limbsEq' hp.litMatch' hp.litFind' hp.litPush' hp.internLit
      hp.romLit n _ c ⟨hS.arena.1.lit.1.2.2.1, hS.arena.1.lit.1.top41⟩) h
  rw [hs'] at hI
  have h := romLitW_core hS c _ hI
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem ls1_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (hd : ∃ l, denoteL a.store.ls (decI u) = some l)
    (h : callW p n "str_ls1" [u] m = some (r, m')) :
    CoreRef (internLsNode [decI u]) a decLs dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strLs1_spec p hp.strLs1 n _ u) h
  have hpool : PoolOK m := hS.arena.1.lit.1
  unfold ls1W at hW
  by_cases hlen : m.len64 (tierA 0 (m.top >>> 40)) ≤ m.top - (m.top >>> 40) <<< 40
  · simp only [hlen, ↓reduceIte] at hW; cases hW
  simp only [hlen, ↓reduceIte] at hW
  cases h1 : callW p n "intern_ls" [m.top, 1]
      ((m.set64 (tierA 0 (m.top >>> 40)) (m.top - (m.top >>> 40) <<< 40) u).set64 CTL 0
        (m.top + 1)) with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  subst hm
  obtain ⟨hg, hpwv, htop⟩ := Grows.push1t m u hpool hlen
  have hK := CoreK.grow (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
    ⟨hS, StackKept.refl _⟩ hg
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = (m.set64 (tierA 0 (m.top >>> 40)) (m.top - (m.top >>> 40) <<< 40)
      u).set64 CTL 0 (m.top + 1) := ⟨_, rfl⟩
  rw [← hm₀] at h1 hK hg hpwv htop
  have hq : SliceOK m₀ m.top 1 := SliceOK.fresh hg htop
  have hk : sliceL (vpool m₀) m.top.toNat (1 : Word).toNat = lsWords [decI u] := by
    simp only [sliceL, lsWords, show (1 : Word).toNat = 1 from rfl]
    simp [hpwv, decI]
    unfold HW at hu
    exact (UInt64.toNat_inj.mp (by simp; omega)).symm
  obtain ⟨s₂, hs₂, -, hI⟩ := triple_of_callW (s₀ := ⟨m₀, Locals.init []⟩)
    (internLs_spec p hp.litHash' hp.limbsEq' hp.lsMatch hp.lsFind hp.lsPush hp.internLs n _ m.top 1
      (by show pcap m₀ < 2 ^ 64; have := hK.1.arena.1.lit.1.2.2.1; omega)
      (by show _ ≤ pcap m₀; have := hK.1.arena.1.lit.1.2.2.2.1; have := hq.1
          omega)) h1
  rw [hs₂] at hI
  obtain ⟨hok, hX, hres⟩ := lsintern_correct m₀ a hK.1.arena.1.lit.1 hK.1.arena.1.ls m.top 1 hq
    [decI u] hk (ModeOK.slice0 hK.1.mode hq) _ _ hI
  have hf := (lsinternW_frame (hI := hI))
  have hLp := lsintern_hp m₀ a hK.1.arena.1.lit.1 hK.1.arena.1.ls m.top 1 hq [decI u] hk
    (ModeOK.slice0 hK.1.mode hq) hK.1.arena.1.lsHp (lsOrW_ok m₀ a hK.1.arena.1 m.top 1 hq [decI u] hk) _ _ hI
  have hI₂ := hI
  have hR' := hK.1.arena.1.lift_ls _ _ _ _ ⟨hX, hLp⟩ hf
    (AM.st_proto lsLens _ _ _ _ _ _ a (internLsNode_run _ a) hok)
  have hL := internLsNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hK.1.of_ls hL hR' hf
    (fun b hb => by simp only [ConsSch.wset, lsCS, lsSch, Option.toList, List.map_nil, List.append_nil, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
    (fun x hx => by simp only [lsCS, lsSch, Option.toList, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
    (lsAll_internLsNode hK.1.arena.1 hK.1.den.lsAll
      (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact hd) (AM.run_of_ok _ _ hok)).1
    (lvlCnt_internLsNode hK.1.arena.1 hR' (hf.2.1 1 (by decide)) (AM.run_of_ok _ _ hok))
  have hw := consInternM_lt lsCS_wf hK.1.arena.1.ls hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hK.2.trans hst⟩, by rw [hres, decLs, hr], by
    unfold ResH; rw [← hr]; exact hw⟩

/-- **`str_ls1` on a readable level makes a readable list** (at the state after it). -/
theorem ls1_den (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "str_ls1" [u] m = some (r, m'))
    (hd : ∃ l, denoteL a.store.ls (decI u) = some l) :
    ∃ ls, denoteLs (AM.st (internLsNode [decI u]) a).store.lss (decI (r.headD 0)) = some ls := by
  have R := ls1_call p hp hS hu hd h
  have hrun := AM.run_of_ok _ _ R.1
  rw [R.2.2.1] at hrun
  exact (denoteLs_internLsNode hS.arena.1
    (fun c hc => by rw [List.mem_singleton] at hc; subst hc; exact hd) hrun).1

end calls

/-! ## Readbacks across steps that keep the level stores -/

theorem lss_st {α : Type} [Inhabited α] {op : AM α} {a : AState} (hk : Keeps cpl op)
    (hok : AM.ok op a) : (AM.st op a).store.lss = a.store.lss :=
  congrArg (fun x => x.2.2) (Keeps.run hk (AM.run_of_ok _ _ hok))

/-- A list readback carried across a step that keeps the level stores. The step's refinement `hc`
may name the step `op'` differently from the caller's `op` (`hop`, by `rfl`): stating the two apart
keeps the unifier from running the step to compare them. -/
theorem lss_den {α : Type} [Inhabited α] {op op' : AM α} {a : AState} {x : LsIdx}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : ∃ ls, denoteLs a.store.lss x = some ls) (hk : Keeps cpl op)
    (hc : CoreRef op' a dec dn m₀ vis fe M eb r m ok) (hop : op = op') :
    ∃ ls, denoteLs (AM.st op a).store.lss x = some ls := by
  subst hop; rw [lss_st hk hc.1]; exact h

/-- A level readback carried across a step that keeps the level stores (as `lss_den`). -/
theorem ls_den {α : Type} [Inhabited α] {op op' : AM α} {a : AState} {x : LIdx}
    {dec : List Word → α} {dn : NIdx → Option ConLeche.Name} {m₀ m : Mem} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : ∃ l, denoteL a.store.ls x = some l) (hk : Keeps cpl op)
    (hc : CoreRef op' a dec dn m₀ vis fe M eb r m ok) (hop : op = op') :
    ∃ l, denoteL (AM.st op a).store.ls x = some l := by
  subst hop
  show ∃ l, denoteL (AM.st op a).store.lss.ls x = some l
  rw [lss_st hk hc.1]; exact h

/-- A list readback carried across a pin read, which keeps the state. -/
theorem lss_pin {op : AM NIdx} {m : Mem} {a : AState} {x : LsIdx} {i : Nat}
    (h : ∃ ls, denoteLs a.store.lss x = some ls) (hpins : PinsFull m a.pins) (hi : i < 51)
    (hop : op = pinAt i) : ∃ ls, denoteLs (AM.st op a).store.lss x = some ls := by
  subst hop
  have hst : AM.st (pinAt i) a = a := by unfold AM.st; rw [pinAt_run hpins i hi]
  rw [hst]; exact h

/-- An interned level reads back (`internLNode_res_den`), the caller's view `v` stated apart from
the refinement's `v'` (as `lss_den`). -/
theorem lnode_den {v v' : LNodeView} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState}
    {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word} {r : List Word} {ok : List Word → Prop}
    (hS : CoreS dn m a vis fe M eb)
    (hch : ∀ c ∈ v.lchildren, ∃ l, denoteL a.store.ls c = some l)
    (hnch : ∀ n ∈ v.nchildren, ∃ x, denoteN a.store.ls.ns n = some x)
    (hc : CoreRef (internLNode v') a decLv dn m vis fe M eb r m' ok) (hv : v = v') :
    ∃ l, denoteL (AM.st (internLNode v) a).store.ls (decI (r.headD 0)) = some l := by
  subst hv
  have h := internLNode_res_den hS hch hnch hc.1
  rw [hc.2.2.1] at h; exact h

/-- A level readback carried across a level interning (`internLNode_lext`). -/
theorem lnode_lvl {v v' : LNodeView} {a : AState} {x : LIdx} {dec : List Word → LIdx}
    {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {vis : Word} {fe : IFEnv} {M : ModeMaps}
    {eb : Word} {r : List Word} {ok : List Word → Prop}
    (h : ∃ l, denoteL a.store.ls x = some l)
    (hc : CoreRef (internLNode v') a dec dn m vis fe M eb r m' ok) (hv : v = v') :
    ∃ l, denoteL (AM.st (internLNode v) a).store.ls x = some l := by
  subst hv
  obtain ⟨l, hl⟩ := h
  exact ⟨l, (internLNode_lext (AM.run_of_ok _ _ hc.1)).lvl _ _ hl⟩

theorem keeps_cpl_pinAt (i : Nat) : Keeps cpl (pinAt i) := by prim_keeps pinAt

theorem keeps_cpl_constE (x : NIdx) : Keeps cpl (constE x) :=
  Keeps.bind (by unfold emptyLevels; prim_keeps pinEmptyLevels) fun _ => keeps_cpl_internConst _ _

/-- The pinned zero level reads back. -/
theorem zero_den {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {w : Word}
    (hw : w = pinW m (53 : Word).toNat) : ∃ l, denoteL a.store.ls (decI w) = some l := by
  subst hw; have := hS.den.zero; rw [hS.pins.zeroLevel] at this; exact this

end L.Arena
