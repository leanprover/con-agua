import ConAgua.Arena.InstLPWalkBase
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.InferBodyIntern
import ConAgua.Arena.InstLPSpec
import ConAgua.Arena.InstLPWalk
import ConAgua.Census.Attr
import ConRon.Bridge.Specs

/-!
# The walk's level arms under `CoreS`: `lv_intern`, `lv_sub_int`, `sl_memo` (helper `whnf4-ilp-lev`)

`LevelInternRef.lean`'s `lvInternW_ok` proves `lv_intern` refines `internLevel` under `ArenaD`;
here the same induction under `CoreS`, without con-ron's `StoreWF`: at each node `CoreS.of_level`
(the node's `LvlStep`, `LvlAll` by `lvlAll_internLNode`, the level tables' growth by
`lvlCnt_of_arena`), so the result reads back (`denoteL`). Then `lv_sub_int` (the heap reset and
`lp_substl` are writers of `LH`, `CTL[192]` alone: `CoreS.frame`), and `sl_memo`: the probe, the
readback (`readLevelM`), the substitution, the memo write (`ILWMemo.setLPL`, `CoreS.frameLP`).
-/

open ConRon.Arena ConLeche
open Std.WP
open scoped Lean.Order


namespace L.Arena

/-! ## The program -/

/-- **What the level arms need of the program**: the walk's functions and the level-list ones. -/
structure ILWLevProg (p : Prog) : Prop where
  ilw : ILWProg p
  ls : LsProg p

/-! ## Small facts -/

theorem LvlStep.trans {a₁ a₂ a₃ : AState} (h₁ : LvlStep a₁ a₂) (h₂ : LvlStep a₂ a₃) : LvlStep a₁ a₃ :=
  ⟨h₂.caches.trans h₁.caches, h₂.pins.trans h₁.pins, h₂.pers.trans h₁.pers, h₂.scr.trans h₁.scr,
    h₂.lsp.trans h₁.lsp, h₂.lss.trans h₁.lss, h₂.lon.trans h₁.lon, h₂.ns.trans h₁.ns,
    ⟨fun i x hx => h₂.ext.ns i x (h₁.ext.ns i x hx), fun i u hu => h₂.ext.lvl i u (h₁.ext.lvl i u hu)⟩,
    h₂.son.trans h₁.son⟩

/-- A level step is a growth of the twin's level stores. -/
theorem LvlStep.grow {a a' : AState} (h : LvlStep a a') : ILWGrow a a' :=
  ⟨lsExt_of_tables h.lsp h.lss h.lon h.ext, h.ns⟩

/-- `internLNode` changes only the store. -/
theorem internLNode_memos (v : LNodeView) (a a' : AState) (h : LIdx)
    (hrun : (internLNode v).run a = .ok (h, a')) : a'.memos = a.memos := by
  unfold internLNode at hrun
  simp only [StateT.run_bind, StateT.run_get, pure_bind] at hrun
  repeat' split at hrun
  all_goals simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
    StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure] at hrun
  all_goals (obtain ⟨-, rfl⟩ := hrun; rfl)

/-- `CoreS` with the level readback cache replaced by one that holds readbacks. -/
theorem CoreS.withReadLC {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) (X : Std.HashMap LIdx Level)
    (hc : ReadLCOK { a with caches := { a.caches with readLC := X } }) :
    CoreS dn m { a with caches := { a.caches with readLC := X } } vis fe M eb :=
  ⟨hS.arena.caches_irrel _, hS.core.readLC X, hS.pins, hS.env, hc, hS.readLs, hS.nwf, hS.erec,
    hS.spn, hS.memos, hS.bstk, hS.den.caches rfl rfl rfl, hS.mode⟩

/-- `CoreS` with the level-list readback cache replaced by one that holds readbacks. -/
theorem CoreS.withReadLsC {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb)
    (X : Std.HashMap LsIdx (List Level))
    (hc : ReadLsCOK { a with caches := { a.caches with readLsC := X } }) :
    CoreS dn m { a with caches := { a.caches with readLsC := X } } vis fe M eb :=
  ⟨hS.arena.caches_irrel _, hS.core.readLsC X, hS.pins, hS.env, hS.readL, hc, hS.nwf, hS.erec,
    hS.spn, hS.memos, hS.bstk, hS.den.caches rfl rfl rfl, hS.mode⟩

section
set_option maxRecDepth 8000
theorem lvArrs_lo : ∀ b ∈ lvArrs, b < 42 ∨ (54 < b ∧ b < 64) ∨ (256 ≤ b ∧ b < 298) ∨ (310 < b ∧ b < 320) := by decide
theorem lvCtl_lo : ∀ x ∈ lvCtl, x.toNat < 42 := by
  intro x hx
  simp only [lvCtl, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
theorem lvArrs_stk : SPN ∉ lvArrs ∧ BSTK ∉ lvArrs ∧ POOL ∉ lvArrs := by decide
theorem lvCtl_stk : (136 : Word) ∉ lvCtl ∧ (137 : Word) ∉ lvCtl ∧ (0 : Word) ∉ lvCtl := by decide
theorem lvCtl_one : (1 : Word) ∉ lvCtl := by decide
end

/-! ## `lv_intern` under `CoreS` -/

section lev
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {M : ModeMaps} {eb : Word}

/-- **What a level interning gives under `CoreS`**: the relation after it, the handle reads
back, and what the caller's frames need. -/
structure LvOut (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (m m' : Mem) (a a' : AState) (h : Word) : Prop where
  core : CoreS dn m' a' vis fe M eb
  hw : HW h
  den : ∃ l, denoteL a'.store.ls (decI h) = some l
  frame : MemFrame lvArrs lvCtl m m'
  keep : LKeep a a'
  views : ViewsKept m m'
  step : LvlStep a a'
  memos : a'.memos = a.memos
  lcnt : LvlCnt m m'

theorem LvOut.stack {m m' : Mem} {a a' : AState} {h : Word} (o : LvOut dn vis fe M eb m m' a a' h) :
    StackKept m m' :=
  StackKept.of_frameL o.frame lvArrs_stk lvCtl_stk o.lcnt

/-- A later level interning after an earlier one: the earlier facts that pass. -/
theorem LvOut.trans {m₁ m₂ m₃ : Mem} {a₁ a₂ a₃ : AState} {h₁ h₂ : Word}
    (o₁ : LvOut dn vis fe M eb m₁ m₂ a₁ a₂ h₁) (o₂ : LvOut dn vis fe M eb m₂ m₃ a₂ a₃ h₂) :
    LvOut dn vis fe M eb m₁ m₃ a₁ a₃ h₂ :=
  ⟨o₂.core, o₂.hw, o₂.den, o₁.frame.trans o₂.frame, o₁.keep.trans o₂.keep, o₁.views.trans o₂.views,
    o₁.step.trans o₂.step, o₂.memos.trans o₁.memos, o₁.lcnt.trans o₂.lcnt⟩


/-- **One node interned under `CoreS`** (the node's children read back). -/
theorem liNode_core (v : LNodeView) (W : Mem → Option (Word × Mem))
    (hop : ∀ m a w m', ArenaD m a → W m = some (w, m') →
      AM.ok (internLNode v) a ∧ ArenaD m' (AM.st (internLNode v) a) ∧ AM.res (internLNode v) a = decI w ∧
        MemFrame lvArrs lvCtl m m')
    {m m' : Mem} {a : AState} {h : Word} (hS : CoreS dn m a vis fe M eb)
    (hch : ∀ c ∈ v.lchildren, ∃ l, denoteL a.store.ls c = some l)
    (hnch : ∀ n ∈ v.nchildren, ∃ x, denoteN a.store.ls.ns n = some x)
    (hW : liNodeK (W m) = some (h, m')) :
    ∃ a', (internLNode v).run a = .ok (decI h, a') ∧ LvOut dn vis fe M eb m m' a a' h := by
  obtain ⟨ok, hR, res, hlt, hf⟩ := liNode_ok (internLNode v) W hop m a h m' hS.arena hW
  have hrun := node_run ok
  rw [res] at hrun
  have hk := internLNode_keep _ _ _ _ hrun
  have hL := internLNode_step _ _ _ _ hrun
  obtain ⟨hall, hden⟩ := lvlAll_internLNode hS.arena.1 hS.den.lvlAll hch hnch hrun
  have hlc := lvlCnt_of_arena hS.arena.1 hR.1 (hf.2.1 1 lvCtl_one)
    (LTGrow.internLNode hrun).1 (LTGrow.internLNode hrun).2 (by simp [hL.lsp]) (by simp [hL.lss])
  obtain ⟨hS', -⟩ := hS.of_level hL hR.1 hf lvArrs_lo lvCtl_lo hall hlc lvArrs_stk.2.2 lvCtl_stk.2.2
  exact ⟨_, hrun, hS', hlt, hden, hf, hk, viewsKept_of hS.arena.1 hR.1 hk hf, hL,
    internLNode_memos _ _ _ _ hrun, hlc⟩

set_option linter.constructorNameAsVariable false in
/-- **The model of `lv_intern` refines `internLevel` under `CoreS`**, of the level the pointer
denotes; the result reads back. -/
theorem lvInternW_core (L : Level) :
    ∀ (n : Nat) (m : Mem) (a : AState) (q h : Word) (m' : Mem),
    CoreS dn m a vis fe M eb → LvR (nameN a.store.lss.ls.ns) m q L →
    lvInternW n m q = some (h, m') →
    ∃ a', (internLevel L).run a = .ok (decI h, a') ∧ LvOut dn vis fe M eb m m' a a' h := by
  induction L with
  | zero =>
    intro n m a q h m' hS hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    have hg : lvG m q = 0 := by cases hl; simp_all [lvG]
    rw [lvInternW_zero n m q hg] at hW
    exact liNode_core .zero zinternW
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.zero_A m a hA w m' hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.1 lvSch_sub.2.1⟩)
      hS (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn => by simp [LNodeView.nchildren] at hn) hW
  | param nm =>
    intro n m a q h m' hS hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, b, hv, hn⟩ : ∃ x b, lvNodeW m q = [4, x, b] ∧ nameN a.store.lss.ls.ns x nm := by
      cases hl with
      | param hv hn => exact ⟨_, _, hv, hn⟩
    have hg : lvG m q = 4 := by simp [lvG, hv]
    have hx : lvA m q = x := by simp [lvA, hv]
    rw [lvInternW_param n m q (by rw [hg]; decide) hg, hx] at hW
    obtain ⟨a', hrun, ho⟩ := liNode_core (.param (decI x)) (fun m => pinternW m x)
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.param_A m a hA w m' x hn.1 hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.2.2⟩)
      hS (fun c hc => by simp [LNodeView.lchildren] at hc)
      (fun n hn => by
        simp only [LNodeView.nchildren, List.mem_cons, List.mem_nil_iff, or_false] at hn
        subst hn; exact ⟨nm, hn.2⟩) hW
    have hN := internName_nameN_run a hS.nwf hn
    refine ⟨a', ?_, ho⟩
    show (internName nm >>= fun hn => internLNode (.param hn)).run a = _
    rw [StateT.run_bind, hN]; exact hrun
  | succ u ih =>
    intro n m a q h m' hS hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, hv, hu⟩ : ∃ x, lvNodeW m q = [1, x, 0] ∧ LvR (nameN a.store.lss.ls.ns) m x u := by
      cases hl with
      | succ hv hu => exact ⟨_, hv, hu⟩
    have hg : lvG m q = 1 := by simp [lvG, hv]
    rw [lvInternW_rec n m q (by rw [hg]; decide) (by rw [hg]; decide), hg,
      show lvA m q = x by simp [lvA, hv]] at hW
    cases hU : lvInternW n m x with
    | none => rw [hU] at hW; simp [liOneK] at hW
    | some r =>
    obtain ⟨hu', m₁⟩ := r
    rw [hU, liOneK_succ n _ _ _ _ rfl] at hW
    obtain ⟨a₁, hrun₁, o₁⟩ := ih n m a x hu' m₁ hS hu hU
    obtain ⟨a', hrun, o⟩ := liNode_core (.succ (decI hu')) (fun m => sinternW m hu')
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.succ_A m a hA w m' hu' o₁.hw hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.1 lvSch_sub.2.2.2.1⟩)
      o₁.core (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
        subst hc; exact o₁.den)
      (fun n hn => by simp [LNodeView.nchildren] at hn) hW
    refine ⟨a', ?_, o₁.trans o⟩
    show (internLevel u >>= fun hu => internLNode (.succ hu)).run a = _
    rw [StateT.run_bind, hrun₁]; exact hrun
  | max u v ihu ihv =>
    intro n m a q h m' hS hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, y, hv, hu, hvv⟩ : ∃ x y, lvNodeW m q = [2, x, y] ∧ LvR (nameN a.store.lss.ls.ns) m x u ∧
        LvR (nameN a.store.lss.ls.ns) m y v := by
      cases hl with
      | max hv hu hw => exact ⟨_, _, hv, hu, hw⟩
    have hg : lvG m q = 2 := by simp [lvG, hv]
    rw [lvInternW_rec n m q (by rw [hg]; decide) (by rw [hg]; decide), hg,
      show lvA m q = x by simp [lvA, hv], show lvB m q = y by simp [lvB, hv]] at hW
    cases hU : lvInternW n m x with
    | none => rw [hU] at hW; simp [liOneK] at hW
    | some r =>
    obtain ⟨hu', m₁⟩ := r
    rw [hU, liOneK_two n _ _ _ _ (by decide)] at hW
    obtain ⟨a₁, hrun₁, o₁⟩ := ihu n m a x hu' m₁ hS hu hU
    have hvv₁ : LvR (nameN a₁.store.lss.ls.ns) m₁ y v := by
      rw [o₁.keep.2]; exact LvR.of_view o₁.views hvv
    cases hV : lvInternW n m₁ y with
    | none => rw [hV] at hW; simp [liTwoK] at hW
    | some r =>
    obtain ⟨hv', m₂⟩ := r
    rw [hV, liTwoK_max _ _ _ _ rfl] at hW
    obtain ⟨a₂, hrun₂, o₂⟩ := ihv n m₁ a₁ y hv' m₂ o₁.core hvv₁ hV
    obtain ⟨a', hrun, o⟩ := liNode_core (.max (decI hu') (decI hv')) (fun m => minternW m hu' hv')
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.max_A m a hA w m' hu' hv' o₁.hw o₂.hw hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.2.2.1 lvSch_sub.2.2.2.2.2.1⟩)
      o₂.core (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨l, hl⟩ := o₁.den; exact ⟨l, o₂.step.ext.lvl _ _ hl⟩
        · exact o₂.den)
      (fun n hn => by simp [LNodeView.nchildren] at hn) hW
    refine ⟨a', ?_, o₁.trans (o₂.trans o)⟩
    show (internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.max hu hv)).run a = _
    rw [StateT.run_bind, hrun₁]; simp only [except_ok_bind]
    rw [StateT.run_bind, hrun₂]; exact hrun
  | imax u v ihu ihv =>
    intro n m a q h m' hS hl hW
    cases n with
    | zero => simp [lvInternW] at hW
    | succ n =>
    obtain ⟨x, y, hv, hu, hvv⟩ : ∃ x y, lvNodeW m q = [3, x, y] ∧ LvR (nameN a.store.lss.ls.ns) m x u ∧
        LvR (nameN a.store.lss.ls.ns) m y v := by
      cases hl with
      | imax hv hu hw => exact ⟨_, _, hv, hu, hw⟩
    have hg : lvG m q = 3 := by simp [lvG, hv]
    rw [lvInternW_rec n m q (by rw [hg]; decide) (by rw [hg]; decide), hg,
      show lvA m q = x by simp [lvA, hv], show lvB m q = y by simp [lvB, hv]] at hW
    cases hU : lvInternW n m x with
    | none => rw [hU] at hW; simp [liOneK] at hW
    | some r =>
    obtain ⟨hu', m₁⟩ := r
    rw [hU, liOneK_two n _ _ _ _ (by decide)] at hW
    obtain ⟨a₁, hrun₁, o₁⟩ := ihu n m a x hu' m₁ hS hu hU
    have hvv₁ : LvR (nameN a₁.store.lss.ls.ns) m₁ y v := by
      rw [o₁.keep.2]; exact LvR.of_view o₁.views hvv
    cases hV : lvInternW n m₁ y with
    | none => rw [hV] at hW; simp [liTwoK] at hW
    | some r =>
    obtain ⟨hv', m₂⟩ := r
    rw [hV, liTwoK_imax _ _ _ _ rfl] at hW
    obtain ⟨a₂, hrun₂, o₂⟩ := ihv n m₁ a₁ y hv' m₂ o₁.core hvv₁ hV
    obtain ⟨a', hrun, o⟩ := liNode_core (.imax (decI hu') (decI hv')) (fun m => iminternW m hu' hv')
      (fun m a w m' hA hI => by
        obtain ⟨ok, hR, res, hf⟩ := L.Front.imax_A m a hA w m' hu' hv' o₁.hw o₂.hw hI
        exact ⟨ok, hR, res, hf.mono lvSch_sub.2.2.2.2.2.2.1 lvSch_sub.2.2.2.2.2.2.2.1⟩)
      o₂.core (fun c hc => by
        simp only [LNodeView.lchildren, List.mem_cons, List.mem_nil_iff, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨l, hl⟩ := o₁.den; exact ⟨l, o₂.step.ext.lvl _ _ hl⟩
        · exact o₂.den)
      (fun n hn => by simp [LNodeView.nchildren] at hn) hW
    refine ⟨a', ?_, o₁.trans (o₂.trans o)⟩
    show (internLevel u >>= fun hu => internLevel v >>= fun hv => internLNode (.imax hu hv)).run a = _
    rw [StateT.run_bind, hrun₁]; simp only [except_ok_bind]
    rw [StateT.run_bind, hrun₂]; exact hrun

/-! ## `lv_sub_int` under `CoreS` -/

/-- **What a successful `lv_sub_int` gives under `CoreS`.** -/
structure SubOut (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps) (eb : Word)
    (m m' : Mem) (a a' : AState) (h : Word) : Prop where
  core : CoreS dn m' a' vis fe M eb
  stack : StackKept m m'
  hw : HW h
  den : ∃ l, denoteL a'.store.ls (decI h) = some l
  grow : ILWGrow a a'
  memos : a'.memos = a.memos
  frame : MemFrame (LH :: lvArrs) (192 :: lvCtl) m m'

/-- **The model of `lv_sub_int` refines `internLevel (Level.subst ks vs l)` under `CoreS`**,
the substitution the walk's (`ILWEnv`). -/
theorem lvSubIntW_core {n : Nat} {m m' : Mem} {a : AState} {u ko kc vo vc h : Word} {L : Level}
    {ks : List Name} {us : List LIdx} {vs : List Level}
    (hS : CoreS dn m a vis fe M eb) (hE : ILWEnv m a ko kc vo vc ks us vs) (hu : HW u)
    (hdu : denoteL a.store.ls (decI u) = some L)
    (hW : lvSubIntW n m u ko kc vo vc = some (h, m')) :
    ∃ a', (internLevel (Level.subst ks vs L)).run a = .ok (decI h, a') ∧
      SubOut dn vis fe M eb m m' a a' h := by
  cases n with
  | zero => simp [lvSubIntW] at hW
  | succ n =>
  simp only [lvSubIntW] at hW
  obtain ⟨hS₀, hk₀⟩ := hS.frame (reset_frame m) (by simp) (by simp)
  have hl : LvR (nameN a.store.lss.ls.ns) (m.set64 CTL 192 0) u L := by
    have := denoteL_lvR hS₀.arena.1 (decI u) L hdu
    rwa [(word_decI _ u hu).mpr rfl] at this
  have hpool₀ : (m.set64 CTL 192 0).arr64 POOL = m.arr64 POOL :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool₀' : (m.set64 CTL 192 0).arr64 POOL1 = m.arr64 POOL1 :=
    Mem.arr64_set64_ne _ _ _ _ _ (by decide)
  have hpool₀v := vpool_congr hpool₀ hpool₀'
  have hpool₀c := pcap_congr' hpool₀ hpool₀'
  have htop := m.top.toNat_lt
  have h41 := hS.arena.1.lit.1.top41
  have hv := lvsR_of_slice hS₀.arena.1 us vs vo vc (by rw [hpool₀v]; exact hE.vals)
    (by have := hE.vtop; omega) hE.vden
  have hk := hE.keys.of_arr (m' := m.set64 CTL 192 0) (Mem.arr64_set64_ne _ _ _ _ _ (by decide))
  cases hSb : substLW SPN POOL n (m.set64 CTL 192 0) u ko kc vo vc with
  | none => rw [hSb] at hW; simp [subIntK] at hW
  | some r =>
  obtain ⟨x, m₁⟩ := r
  rw [hSb, subIntK_some] at hW
  obtain ⟨he, hx⟩ := substLW_ok (nameN_rel _ hS.nwf) (KA := SPN) (VA := POOL) (by decide) (by decide)
    ks vs n _ _ _ _ _ _ _ _ _ hl hk hv.toAR hSb
  obtain ⟨hS₁, hk₁⟩ := hS₀.frame he.memFrame (by simp [LH]) (by simp)
  obtain ⟨a', hrun, o⟩ := lvInternW_core _ n m₁ a x h m' hS₁ hx hW
  refine ⟨a', hrun, o.core, hk₀.trans (hk₁.trans o.stack), o.hw, o.den, o.step.grow, o.memos, ?_⟩
  exact ((reset_frame m).mono (by simp) (by simp)).trans
    ((he.memFrame.mono (by simp) (by simp)).trans
      (o.frame.mono (fun b hb => List.mem_cons_of_mem _ hb) (fun x hx => List.mem_cons_of_mem _ hx)))

end lev

/-! ## `sl_memo` -/

/-- The walk memos at a state with the same memos and store. -/
theorem ILWMemo.congr {m : Mem} {a a' : AState} (h : ILWMemo m a) (hme : a'.memos = a.memos)
    (hst : a'.store = a.store) : ILWMemo m a' :=
  h.frame (MemFrame.refl [] [] m) (by decide) (by decide) hme (ILWGrow.of_lss (by rw [hst]))

/-- The substitution at a state with the same store. -/
theorem ILWEnv.congr {m : Mem} {a a' : AState} {ko kc vo vc : Word} {ks : List Name}
    {us : List LIdx} {vs : List Level} (h : ILWEnv m a ko kc vo vc ks us vs)
    (hst : a'.store = a.store) : ILWEnv m a' ko kc vo vc ks us vs :=
  h.keep (StackKept.refl m) (ILWGrow.of_lss (by rw [hst]))

/-- **`sl_memo` refines `substLMemoAt`** under the walk's invariants. -/
@[refines ConRon.Arena.substLMemoAt]
theorem slMemo_ok (p : Prog) (hp : ILWLevProg p) : SlMemoOK p := by
  intro n m m' a dn vis fe M eb u ko kc vo vc ks us vs rs hS hM hE hu hdu' hc
  obtain ⟨L, hdu⟩ := hdu'
  cases n with
  | zero => rw [callW_zero] at hc; cases hc
  | succ k =>
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slMemo_spec p hp.ilw k _ u ko kc vo vc) hc
  rw [hs'] at hW
  change ilwSlW p k m u ko kc vo vc = some (rs.headD 0, m') at hW
  unfold ilwSlW at hW
  have hr : ¬ mfindG lplSch m u 0 = [] := fun hr => by simp [hr] at hW
  simp only [hr, ↓reduceIte] at hW
  by_cases hh : (mfindG lplSch m u 0).headD 0 ≠ 0
  · -- a hit: the memo's value
    simp only [ne_eq, hh, not_false_eq_true, ↓reduceIte] at hW
    obtain ⟨hw, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    obtain ⟨v, hv, hvv, hvl⟩ := memoRV_hit lplSch ilKey VI m _ hM.lpl u 0 hr hh ⟨hu, rfl⟩
    have hval : mvG lplSch m ((mfindG lplSch m u 0).tail.headD 0) = rs.headD 0 := hw
    rw [hval] at hvv hvl
    have hget : a.memos.instLPLC[(decI u : LIdx)]? = some (decI (rs.headD 0)) := by
      rw [← hvv]; exact hv
    refine ⟨a, ?_, ⟨M, hS, KeptAll.refl _ _, StackKept.refl _⟩, hM, ILWGrow.refl a, hvl,
      hM.lplDen _ _ hget⟩
    simp only [substLMemoAt, StateT.run_bind, instLPLGet_run, except_ok_bind, hget]; rfl
  -- a miss: read back, substitute, record
  simp only [hh, ↓reduceIte] at hW
  have hmiss : a.memos.instLPLC[(decI u : LIdx)]? = none :=
    memoRV_miss lplSch ilKey VI m _ hM.lpl u 0 ⟨hu, rfl⟩ hr (by simpa using hh)
  cases h1 : callW p k "lv_sub_int" [u, ko, kc, vo, vc] m with
  | none => rw [h1] at hW; simp [ilwSlK] at hW
  | some q =>
  obtain ⟨r₁, m₁⟩ := q
  rw [h1, ilwSlK_some] at hW
  obtain ⟨s₁, hs₁, -, hW₁⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvSubInt_spec p hp.ls.toLvSubProg k _ u ko kc vo vc) h1
  rw [hs₁] at hW₁
  obtain ⟨X, hrl, hrc⟩ := readLevelM_run' a (decI u) L hdu hS.readL
  have hSR := hS.withReadLC X hrc
  obtain ⟨a₁, hrun₁, o⟩ := lvSubIntW_core hSR (hE.congr rfl) hu hdu hW₁
  have hb : ¬ 4294967296 ≤ r₁.headD 0 := fun hb => by simp only [hb, ↓reduceIte] at hW; cases hW
  simp only [hb, ↓reduceIte] at hW
  rcases h2 : msetG lplSch m₁ u 0 (r₁.headD 0) with _ | m₂ <;> simp only [h2, reduceCtorEq] at hW
  obtain ⟨hr₁, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  rw [← hr₁]
  have hM₁ : ILWMemo m₁ a₁ := ILWMemo.frame (a := { a with caches := { a.caches with readLC := X } })
    (hM.congr rfl rfl) o.frame (by decide) (by decide) o.memos o.grow
  have hM₂ := hM₁.setLPL u (r₁.headD 0) hu o.hw o.den h2
  have hf₂ := msetG_frame lplSch lplSch_wf m₁ m₂ u 0 _ h2
  have hf₂' : MemFrame [lplSch.arr] [lplSch.cs, lplSch.cs + 1] m₁ m₂ := hf₂.mono (by simp) (by simp)
  obtain ⟨hS₂, hk₂⟩ := CoreS.frameLP lplSch (.inr (.inl rfl)) o.core hf₂'
    (o.core.memos.frameLP hf₂' hM₂.lpMemos (by decide) (by simp))
  refine ⟨_, ?_, ⟨M, hS₂.lpMemos a₁.memos.instLPC
      (a₁.memos.instLPLC.insert (decI u) (decI (r₁.headD 0))) a₁.memos.instLPLsC,
    KeptAll.refl _ _, o.stack.trans hk₂⟩, hM₂, ?_, o.hw, o.den⟩
  · simp only [substLMemoAt, StateT.run_bind, instLPLGet_run, except_ok_bind, hmiss, hrl, hrun₁,
      instLPLSet_run]; rfl
  · exact ILWGrow.trans (a₂ := a₁) (ILWGrow.trans (a₂ := { a with caches := { a.caches with readLC := X } })
      (ILWGrow.of_lss rfl) o.grow) (ILWGrow.of_lss rfl)

end L.Arena
