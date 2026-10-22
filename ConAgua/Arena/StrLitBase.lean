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

theorem internLsNode_step (v : LsNodeView) (a a' : AState) (h : LsIdx)
    (hrun : (internLsNode v).run a = .ok (h, a')) : LsStep a a' := by
  unfold internLsNode at hrun
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrun
  repeat' split at hrun
  all_goals simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
    StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure] at hrun
  all_goals first
    | (obtain ⟨-, rfl⟩ := hrun; exact ⟨rfl, rfl, rfl, rfl, rfl, fun _ _ h => h⟩)
    | (obtain ⟨-, rfl⟩ := hrun
       exact ⟨rfl, rfl, rfl, rfl, LsStore.ls_intern _ _,
         fun _ _ h => LsStore.view_intern_mono _ _ h⟩)

/-- **`CoreS` across a level-list interning** whose memory writes are confined to the level
stores' arrays (below 42) and counts (`CTL` below 42). -/
theorem CoreS.of_ls {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a a' : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} {A : List ArrId} {C : List Word}
    (hS : CoreS dn m a vis fe M eb) (hL : LsStep a a') (hR : ArenaR m' a')
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42) (hC : ∀ x ∈ C, x.toNat < 42) :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => .inl (hA b hb)) a hS.arena.2) hL.pers hL.scr
  have hspn : m'.arr64 SPN = m.arr64 SPN :=
    hf.1 SPN (fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega) (by decide)
  have h136 : rdW (m'.arr64 CTL) 136 = rdW (m.arr64 CTL) 136 :=
    hf.2.1 136 (fun h => by have := hC _ h; simp at this)
  refine ⟨⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
      (fun x hx => .inl (by have := hC x hx; omega)) hf, ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
      hS.memos.frame hf ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩,
      hf.2.2.1 145 ▸ hS.bstk⟩,
    by simp only [spTop, h136], by rw [hspn], fun i _ => by simp only [spW, hspn]⟩
  · rw [hL.caches]
    exact CoreRM.frame (A := A) (C := C) (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
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
    (rs : List Word) (hI : pinternW m u = some (rs.headD 0, m')) :
    CoreRef (internLNode (.param (decI u))) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := pintern_correct m a hS.arena.1.param u hu _ _ hI
  have hI₂ := hI; rw [pinternW_eq] at hI₂
  have hf := internM_frame _ paramSch_wf _ _ _ _ _ _ _ _ hI₂
  have hR' := hS.arena.1.lift_param _ _ _ _ hX hf
    (AM.st_proto paramLens _ _ _ _ _ _ a (internLNode_param_run _ a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [paramSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [paramSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hw := internM_hw paramSch PRecRel phash paramSch_wf m _ _ _ hS.arena.1.param (pMt m u) _ _ _ _
    (probe_homeG paramSch m 0 _ _ (pprobeW_arm m u 0) _)
    (probe_homeG paramSch m 1 _ _ (pprobeW_arm m u 1) _) _ (ppushOK_room m) _ _ _ m' hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

/-- **`intern_zero` refines `internLNode .zero` under `CoreS`.** -/
theorem internZero_core (hS : CoreS dn m a vis fe M eb)
    (rs : List Word) (hI : zinternW m = some (rs.headD 0, m')) :
    CoreRef (internLNode .zero) a decLv dn m vis fe M eb rs m' := by
  obtain ⟨hok, hX, hres⟩ := zintern_correct m a hS.arena.1.zero _ _ hI
  have hI₂ := hI; rw [zinternW_eq] at hI₂
  have hf := internM_frame _ zeroSch_wf _ _ _ _ _ _ _ _ hI₂
  have hR' := hS.arena.1.lift_zero _ _ _ _ hX hf
    (AM.st_proto zeroLens _ _ _ _ _ _ a (internLNode_zero_run a) hok)
  have hL := internLNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hS.of_level hL hR' hf
    (fun b hb => by simp only [zeroSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [zeroSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hw := internM_hw zeroSch ZRecRel zhash zeroSch_wf m _ _ _ hS.arena.1.zero (zMt m) _ _ _ _
    (probe_homeG zeroSch m 0 _ _ (zprobeW_arm m 0) _)
    (probe_homeG zeroSch m 1 _ _ (zprobeW_arm m 1) _) _ (zpushOK_room m) _ _ _ m' hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hst⟩, by rw [hres]; rfl, hw⟩

end leaves

/-! ## A `lit` interning under `CoreS` -/

section litc
variable {dn : NIdx → Option ConLeche.Name} {m m₀ m' : Mem} {a : AState} {vis : Word}
  {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- **`internW` under `CoreK`**: the twin's `lit` interning of the slice's value. -/
theorem internW_core (hK : CoreK dn vis fe M eb m₀ m a) (o l : Word) (hq : SliceOK m o l)
    (hn : Norm (m.arr64 POOL) o.toNat l.toNat) (w : Word) (hI : internW m o l = some (w, m')) :
    CoreRef (internE (.lit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat)))) a
      (fun r => decE (r.headD 0)) dn m₀ vis fe M eb [w] m' := by
  obtain ⟨hok, hD, hres⟩ := internLit_D m a hK.1.arena o l _ hq hn _ hI
  have hI₂ := hI; rw [internW_eq] at hI₂
  have hfr := internM_frame _ litS_wf _ _ _ _ _ _ _ _ hI₂
  simp only [litSch] at hfr
  have hcpl := (keeps_cpl_internLit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))).run
    (AM.run_of_ok _ _ hok)
  refine ⟨hok, ⟨M, hK.1.arena_frame hD hcpl hfr ?_ ?_ ?_ ?_ ?_,
    KeptAll.refl _ _, hK.2.trans (StackKept.of_frame hfr (by simp [REC, SLOT, SPN]) (by simp))⟩,
    hres, internW_hw m a hK.1.arena.1.lit o l w m' hI⟩
  · intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl <;> decide
  · simp [REC, SLOT, PINS]
  · intro b hb; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
    rcases hb with rfl | rfl <;> decide
  · intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> decide
  · intro x hx; simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl <;> decide

theorem pv_one (p : Array Word) (o : Nat) : pv p o 1 = (p[o]?.getD 0).toNat := by
  simp [pv, wt]

/-- **`rom_lit(c)`'s model under `CoreS`**: the twin's `Nat` literal `c`. -/
theorem romLitW_core (hS : CoreS dn m a vis fe M eb) (c w : Word) (hI : L.Rom.romLitW m c = some (w, m')) :
    CoreRef (internE (.lit (.natVal c.toNat))) a decH dn m vis fe M eb [w] m' := by
  have hpool : PoolOK m := hS.arena.1.lit.1
  unfold L.Rom.romLitW at hI
  by_cases hlen : m.len64 POOL ≤ m.top
  · rw [if_pos hlen] at hI; cases hI
  rw [if_neg hlen] at hI
  have hlt : m.top.toNat < (m.arr64 POOL).size := by
    simp only [Mem.len64, UInt64.le_iff_toNat_le, Nat.not_le] at hlen
    have := hpool.2.2.1
    rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)] at hlen; exact hlen
  by_cases hc : c = 0
  · rw [if_pos hc] at hI
    have h := internW_core (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
      ⟨hS, StackKept.refl _⟩ m.top 0 (by simp [SliceOK]) (by simp [Norm]) w hI
    subst hc
    simpa [pv] using h
  · rw [if_neg hc] at hI
    have hg := Grows.push1 m m.top c rfl hpool hlt
    have hK := CoreK.grow (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
      ⟨hS, StackKept.refl _⟩ hg
    have htop : (L.Rom.litWordMem m c).top = m.top + 1 := by
      unfold L.Rom.litWordMem
      exact Mem.top_set64 _ _ (by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hpool.2.1)
    have hpw : ((L.Rom.litWordMem m c).arr64 POOL)[m.top.toNat]? = some c := by
      unfold L.Rom.litWordMem
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_same]
      simp [hlt]
    have h := internW_core hK m.top 1 (by
        simp only [SliceOK, htop]; rw [UInt64.toNat_add]; simp; omega)
      (by intro _; simp [hpw, hc]) w hI
    have hv : pv ((L.Rom.litWordMem m c).arr64 POOL) m.top.toNat (1 : Word).toNat = c.toNat := by
      simp [pv_one, hpw]
    rw [hv] at h; exact h

end litc

end L.Arena
