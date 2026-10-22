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
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, b < 42) (hC : ∀ x ∈ C, x.toNat < 42)
    (hP : POOL ∉ A := by decide) (hP0 : (0 : Word) ∉ C := by decide) :
    CoreS dn m' a' vis fe M eb ∧ StackKept m m' := by
  have hD : DerR m' a' := DerR.of_tiers m' a a'
    (DerR.frameM A C m m' hf (fun b hb => .inl (hA b hb)) a hS.arena.2) hL.pers hL.scr
  refine ⟨⟨⟨hR, hD⟩, ?_, ?_, hS.env.frame (fun b hb => .inl (by have := hA b hb; simp only [ArrId] at this ⊢; omega))
      (fun x hx => .inl (by have := hC x hx; omega)) hf, ?_, ?_, ?_,
      hf.2.2.1 EREC ▸ hS.erec, hf.2.2.1 SPN ▸ hS.spn,
      hS.memos.frame hf ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide)⟩
        ⟨fun h => absurd (hA _ h) (by decide), fun h => absurd (hA _ h) (by decide),
          fun h => absurd (hA _ h) (by decide)⟩
        ⟨fun h => absurd (hC _ h) (by decide), fun h => absurd (hC _ h) (by decide),
          fun h => absurd (hC _ h) (by decide)⟩,
      hf.2.2.1 145 ▸ hS.bstk⟩,
    StackKept.of_frame hf
      ⟨fun h => by have := hA _ h; simp only [SPN, ArrId] at this; omega,
       fun h => by have := hA _ h; simp only [BSTK, ArrId] at this; omega, hP⟩
      ⟨fun h => by have := hC _ h; simp at this, fun h => by have := hC _ h; simp at this, hP0⟩⟩
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
      decH dn m₀ vis fe M eb [w] m' := by
  obtain ⟨hok, hD, hres⟩ := internLit_D m a hK.1.arena o l _ hq hn _ hI
  have hI₂ := hI; rw [internW_eq] at hI₂
  have hfr := internM_frame _ litS_wf _ _ _ _ _ _ _ _ hI₂
  simp only [litSch] at hfr
  have hcpl := (keeps_cpl_internLit (.natVal (pv (m.arr64 POOL) o.toNat l.toNat))).run
    (AM.run_of_ok _ _ hok)
  refine ⟨hok, ⟨M, hK.1.arena_frame hD hcpl hfr ?_ ?_ ?_ ?_ ?_,
    KeptAll.refl _ _, hK.2.trans (StackKept.of_frame hfr)⟩,
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
    simp only [L.Rom.litWordMem] at hI
    have hg := Grows.push1 m m.top c rfl hpool hlt
    have hK := CoreK.grow (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
      ⟨hS, StackKept.refl _⟩ hg
    have htop : ((m.set64 POOL m.top c).set64 CTL 0 (m.top + 1)).top = m.top + 1 :=
      Mem.top_set64 _ _ (by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hpool.2.1)
    have hpw : (((m.set64 POOL m.top c).set64 CTL 0 (m.top + 1)).arr64 POOL)[m.top.toNat]? =
        some c := by
      rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_same]
      simp [hlt]
    have hq : SliceOK ((m.set64 POOL m.top c).set64 CTL 0 (m.top + 1)) m.top 1 := by
      have : (m.top + 1).toNat = m.top.toNat + 1 := by
        rw [UInt64.toNat_add]; simp; have := hpool.2.2.1; omega
      simp only [SliceOK, htop, this]; simp
    have h := internW_core hK m.top 1 hq (by intro _; simp [hpw, hc]) w hI
    have hv : pv (((m.set64 POOL m.top c).set64 CTL 0 (m.top + 1)).arr64 POOL) m.top.toNat
        (1 : Word).toNat = c.toNat := by
      simp [pv, wt, hpw]
    rw [hv] at h; exact h

end litc

/-! ## `str_ls1` -/

/-- The model of `str_ls1`. -/
def ls1W (p : Prog) (n : Nat) (m : Mem) (u : Word) : Option (Word × Mem) :=
  if m.len64 POOL ≤ m.top then none
  else match callW p n "intern_ls" [m.top, 1] ((m.set64 POOL m.top u).set64 CTL 0 (m.top + 1)) with
    | none => none
    | some (r, m') => some (r.headD 0, m')

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
    (h : callW p n "intern_param" [u] m = some (r, m')) :
    CoreRef (internLNode (.param (decI u))) a decLv dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internParam_spec p hp.paramFind hp.paramPush hp.internParam n _ u) h
  rw [hs'] at hI
  exact internParam_core hS u hu r hI

theorem succ_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "intern_succ" [u] m = some (r, m')) :
    CoreRef (internLNode (.succ (decI u))) a decLv dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSucc_spec p hp.succFind hp.succPush hp.internSucc n _ u) h
  rw [hs'] at hI
  exact internSucc_core hS u hu r hI

theorem zero_call (hS : CoreS dn m a vis fe M eb)
    (h : callW p n "intern_zero" [] m = some (r, m')) :
    CoreRef (internLNode .zero) a decLv dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internZero_spec p hp.zeroFind hp.zeroPush hp.internZero n _) h
  rw [hs'] at hI
  exact internZero_core hS r hI

theorem sort_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "intern_sort" [u] m = some (r, m')) :
    CoreRef (internE (.sort (decI u))) a decH dn m vis fe M eb r m' := by
  obtain ⟨s', hs', -, hI⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (internSort_spec p hp.sortFind hp.sortPush hp.internSort n _ u) h
  rw [hs'] at hI
  exact internSort_core hS u hu r hI

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
    (h : callW p n "intern_const" [f, x] m = some (r, m')) :
    CoreRef (internE (.const (decI f) (decI x))) a decH dn m vis fe M eb r m' := by
  obtain ⟨hok, hD, hres, hfr, hhw⟩ := callW_internConst p hp.constFind' hp.constPush' hp.internConst
    n ⟨m, Locals.init []⟩ a hS.arena f x hf hx r m' h
  exact ⟨hok, ⟨M, hS.of_const hD (Keeps.run (keeps_cpl_internConst _ _) (AM.run_of_ok _ _ hok)) hfr,
    KeptAll.refl _ _, StackKept.of_const_frame hfr⟩, hres, hhw⟩

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
      hp.romLit n _ c (by have := hS.arena.1.lit.1.2.2.1; simp only at this ⊢; omega)) h
  rw [hs'] at hI
  have h := romLitW_core hS c _ hI
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem ls1_call (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u)
    (h : callW p n "str_ls1" [u] m = some (r, m')) :
    CoreRef (internLsNode [decI u]) a decLs dn m vis fe M eb r m' := by
  cases n with
  | zero => rw [callW_zero] at h; cases h
  | succ n =>
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (strLs1_spec p hp.strLs1 n _ u) h
  have hpool : PoolOK m := hS.arena.1.lit.1
  unfold ls1W at hW
  by_cases hlen : m.len64 POOL ≤ m.top
  · simp only [hlen, ↓reduceIte] at hW; cases hW
  simp only [hlen, ↓reduceIte] at hW
  have hlt : m.top.toNat < (m.arr64 POOL).size := by
    simp only [Mem.len64, UInt64.le_iff_toNat_le, Nat.not_le] at hlen
    have := hpool.2.2.1
    rw [UInt64.toNat_ofNat_of_lt' (by simp [UInt64.size]; omega)] at hlen; exact hlen
  cases h1 : callW p n "intern_ls" [m.top, 1] ((m.set64 POOL m.top u).set64 CTL 0 (m.top + 1)) with
  | none => rw [h1] at hW; cases hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨hr, hm⟩ := hW
  subst hm
  have hg := Grows.push1 m m.top u rfl hpool hlt
  have hK := CoreK.grow (dn := dn) (vis := vis) (fe := fe) (M := M) (eb := eb) (m₀ := m)
    ⟨hS, StackKept.refl _⟩ hg
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = (m.set64 POOL m.top u).set64 CTL 0 (m.top + 1) := ⟨_, rfl⟩
  rw [← hm₀] at h1 hK
  have htop : m₀.top = m.top + 1 := by
    rw [hm₀]
    exact Mem.top_set64 _ _ (by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)]; exact hpool.2.1)
  have hpw : (m₀.arr64 POOL)[m.top.toNat]? = some u := by
    rw [hm₀, Mem.arr64_set64_ne _ _ _ _ _ (by decide), Mem.arr64_set64_same]
    simp [hlt]
  have hq : SliceOK m₀ m.top 1 := by
    have : (m.top + 1).toNat = m.top.toNat + 1 := by
      rw [UInt64.toNat_add]; simp; have := hpool.2.2.1; omega
    simp only [SliceOK, htop, this]; simp
  have hk : sliceL (m₀.arr64 POOL) m.top.toNat (1 : Word).toNat = lsWords [decI u] := by
    simp only [sliceL, lsWords, show (1 : Word).toNat = 1 from rfl]
    simp [hpw, decI]
    unfold HW at hu
    exact (UInt64.toNat_inj.mp (by simp; omega)).symm
  obtain ⟨s₂, hs₂, -, hI⟩ := triple_of_callW (s₀ := ⟨m₀, Locals.init []⟩)
    (internLs_spec p hp.litHash' hp.limbsEq' hp.lsMatch hp.lsFind hp.lsPush hp.internLs n _ m.top 1
      (by show (m₀.arr64 POOL).size < 2 ^ 64; have := hK.1.arena.1.lit.1.2.2.1; omega)
      (by show _ ≤ (m₀.arr64 POOL).size; have := hK.1.arena.1.lit.1.2.2.2; simp only [SliceOK] at hq
          omega)) h1
  rw [hs₂] at hI
  obtain ⟨hok, hX, hres⟩ := lsintern_correct m₀ a hK.1.arena.1.lit.1 hK.1.arena.1.ls m.top 1 hq
    [decI u] hk _ _ hI
  have hI₂ := hI; rw [lsinternW_eq] at hI₂
  have hf := internM_frame _ lsSch_wf _ _ _ _ _ _ _ _ hI₂
  have hR' := hK.1.arena.1.lift_ls _ _ _ _ hX hf
    (AM.st_proto lsLens _ _ _ _ _ _ a (internLsNode_run _ a) hok)
  have hL := internLsNode_step _ a _ _ (AM.run_of_ok _ _ hok)
  obtain ⟨hS', hst⟩ := hK.1.of_ls hL hR' hf
    (fun b hb => by simp only [lsSch, List.mem_cons, List.mem_nil_iff, or_false] at hb
                    rcases hb with rfl | rfl <;> decide)
    (fun x hx => by simp only [lsSch, List.mem_cons, List.mem_nil_iff, or_false] at hx
                    rcases hx with rfl | rfl <;> decide)
  have hw := internM_hw lsSch LsRecRel lshash lsSch_wf m₀ _ _ _ hK.1.arena.1.ls
    (lsMt m₀ m.top 1 (hashN (m₀.arr64 POOL) m.top.toNat (1 : Word).toNat)) _ _ _ _
    (probe_homeG lsSch m₀ 0 _ _ (lsprobeW_arm m₀ m.top 1 _ 0) _)
    (probe_homeG lsSch m₀ 1 _ _ (lsprobeW_arm m₀ m.top 1 _ 1) _) _ (lspushOK_room m₀) _ _ _ _ hI₂
  exact ⟨hok, ⟨M, hS', KeptAll.refl _ _, hK.2.trans hst⟩, by rw [hres, decLs, hr], by
    unfold ResH; rw [← hr]; exact hw⟩

end calls

end L.Arena
