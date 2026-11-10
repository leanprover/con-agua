module

import ConAgua.Arena.KnotMono
import ConAgua.Arena.WhnfCoreRefine
public import ConAgua.Arena.WhnfM2CRefine2
import ConAgua.Checker.NoVerdictTree
import ConRon.Bridge.Rel
import ConAgua.Arena.RefWalk
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import all ConAgua.Arena.Infer
import all ConAgua.Arena.LevelZero
import ConRon.Bridge.Grind
import ConAgua.Front.Preserve
import ConAgua.L.WordOff

@[expose] public section

/-!
# The projection's guard at the use: `check_proj_guard` (`checkProjGuard`)

One unified model and one refinement for both outcomes per knot-reaching function:
`proj_guard_sort` (`pgs_ref`; `former_sort_loop` through its unified model, as `fnza_ref`),
`check_guard_rows` (`cgr_ref`; the `infer_io`/`whnf` slots through their runs, the recursion inside
the model), `check_proj_guard` (`cpg_ref`). `proj_guard_rows` reaches no slot: its lifted run
refines `projGuardRows` (`pgr_ok`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-- **`proj_guard_sort`'s unified model** (`former_sort_loop` through its unified model, the other
callees lifted). -/
l_model pgsE_spec (p : Prog) (hf : p.lookup "proj_guard_sort" = some projGuardSortL)
  (hs : p.lookup "former_sort_loop" = some formerSortLoopL)
  fns [hf ↦ pgsE list]
  specs [callW_spec p n "former_res_sort", callW_spec p n "lv_always_zero", callW_spec p n "pin_word",
    callW_spec p n "inst_lp", fslE_spec p hs n, callW_spec p n "lv_never"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_guard_rows`' unified model** (the `infer_io`/`whnf` slots and the recursive call
through their runs, `lv_zero_where_zero` lifted). -/
l_model cgrE_spec (p : Prog) (hf : p.lookup "check_guard_rows" = some checkGuardRowsL)
  fns [hf ↦ cgrE list]
  specs [callW_spec p n "lv_zero_where_zero"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`check_proj_guard`'s unified model** (`proj_guard_sort` and `check_guard_rows` through their
unified models, `env_find` and `proj_guard_rows` lifted). -/
l_model cpgE_spec (p : Prog) (hf : p.lookup "check_proj_guard" = some checkProjGuardL)
  (hs : p.lookup "former_sort_loop" = some formerSortLoopL)
  (hg : p.lookup "proj_guard_sort" = some projGuardSortL)
  (hc : p.lookup "check_guard_rows" = some checkGuardRowsL)
  fns [hf ↦ cpgE list]
  specs [callW_spec p n "env_find", pgsE_spec p hg hs n, callW_spec p n "proj_guard_rows",
    cgrE_spec p hc n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- **`lv_always_zero`'s model**: `lv_zero` lifted, the heap top put back. -/
l_model lvAzW_spec (p : Prog) (hf : p.lookup "lv_always_zero" = some lvAlwaysZero)
  fns [hf ↦ lvAzW] specs [callW_spec p n "lv_zero"] grind [arena_grind] fold [tierW, idxW]

/-- **`lv_zero_where_zero`'s model** (`lv_zero`, `lh_contains` lifted). -/
l_model lvZwzW_spec (p : Prog) (hf : p.lookup "lv_zero_where_zero" = some lvZeroWhereZero)
  fns [hf ↦ lvZwzW] specs [callW_spec p n "lv_zero", callW_spec p n "lh_contains"]
  grind [arena_grind] fold [tierW, idxW]

/-- **`lh_contains`' model** (the loop over the heap slice). -/
l_model lhcW_spec (p : Prog) (hf : p.lookup "lh_contains" = some lhContains)
  fns [hf ↦ lhcW] grind [arena_grind] fold [tierW, idxW]

/-- **`lv_always_zero` is `ConLeche.Level.isAlwaysZero` under `CoreS`** (the heap top put back). -/
theorem lvAz_core {p : Prog} (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {u : Word} (hu : HW u) {L : ConLeche.Level}
    (hd : denoteL a.store.ls (decI u) = some L) {w : Word}
    (h : lvAzW p n m u = some (w, m')) :
    w = (if L.isAlwaysZero then 1 else 0) ∧ CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
  rcases n with _ | n
  · simp [lvAzW] at h
  rw [lvAzW.arm1] at h
  rcases hc : callW p n "lv_zero" [u] m with _ | ⟨r, m₁⟩
  · rw [hc, lvAzW.k_lv_zero.none] at h; cases h
  rw [hc, lvAzW.k_lv_zero.arm1] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨s', hs', -, hz⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m, Locals.init []⟩ u) hc
  rw [hs'] at hz
  have hl := denoteL_lvR hS.arena.base (decI u) L hd
  rw [decI_word_self u hu] at hl
  obtain ⟨he, hZ⟩ := zeroW_ok n _ _ _ _ _ hl hz
  have hf : MemFrame [LH] [192] m (m₁.set64 CTL 192 (rdW (m.arr64 CTL) 192)) :=
    he.memFrame.trans ((MemFrame.setCtl m₁ 192 _).mono (by simp) (by simp))
  obtain ⟨hS', hK⟩ := hS.frame hf (by simp [LH]) (by simp)
  refine ⟨?_, hS', hK⟩
  unfold ConLeche.Level.isAlwaysZero
  rcases hZ with ⟨hx, hpw⟩ | ⟨hx, ps, hpw, hN⟩
  · rw [hx, hpw]; simp
  · rw [hx, hpw]
    generalize hk : htop m₁ - htop m = k at hN
    cases hN with
    | nil =>
      have : htop m₁ = htop m := by grind
      simp only [htop] at this
      simp [this]
    | cons hk0 _ _ =>
      have : htop m₁ ≠ htop m := fun e => hk0 (by rw [← hk, e]; simp)
      simp only [htop] at this
      simp [this]

/-! ## The guard sort -/

/-- **The guard sort's word against the twin's level**: a handle whose readback has the twin's
level's zero-ness (all `check_guard_rows` asks of it, `ConLeche.Level.zeroWhereZero` reading only the
zero-ness of its first level). -/
def GsDen (a : AState) (gs : Word) (l : ConLeche.Level) : Prop :=
  HW gs ∧ ∃ l', denoteL a.store.ls (decI gs) = some l' ∧ ConLeche.Level.zeronessOf l' = ConLeche.Level.zeronessOf l

/-- `proj_guard_sort`'s words against `projGuardSort`'s answer: `(0, _)` none, `(1, gs)` the
guard sort. -/
def PgsRes (a : AState) (r : List Word) : Option ConLeche.Level → Prop
  | none => r.headD 0 = 0
  | some l => r.headD 0 ≠ 0 ∧ GsDen a (r.tail.headD 0) l

/-- `proj_guard_sort`'s post: the relation after, the answer. -/
structure PgsPost (dn : NIdx → Option ConLeche.Name) (m₀ : Mem) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word) (v : List Word × Mem) (y : Option ConLeche.Level) (a' : AState) : Prop where
  after : CoreAfter dn m₀ v.2 a' vis fe M eb
  res : PgsRes a' v.1 y

theorem ErrClaim.of_error {α : Type} {T : AM α} {a : AState} {e : Err} {ce : CheckError}
    (h : T.run a = .error ce) (hk : e.cls = twinCls ce) : ErrClaim T a e :=
  fun _ => ⟨ce, h, hk.symm⟩

theorem PgsPost.comp {dn : NIdx → Option ConLeche.Name} {m₀ m₁ : Mem} {vis : Word} {fe : IFEnv}
    {M M' : ModeMaps} {eb : Word} (hK : KeptAll M M' eb) (hSt : StackKept m₀ m₁)
    (v : List Word × Mem) (y : Option ConLeche.Level) (a' : AState)
    (h : PgsPost dn m₁ vis fe M' eb v y a') : PgsPost dn m₀ vis fe M eb v y a' :=
  ⟨CoreAfter.comp hK hSt h.after, h.res⟩

/-- **The pinned zero level reads back as `ConLeche.Level.zero`** (con-ron's `PinsOK.zeroLevel`,
`StoreDen.zero`). -/
theorem zeroPin_den {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) :
    denoteL a.store.ls (decI (rdW (m.arr64 PINS) 53)) = some .zero := by
  have := hS.den.zero; rw [hS.pins.zeroLevel, pinW_rdW m 53 53 rfl] at this; exact this

/-- `formerSortLoop` reads its record only through `whnf`. -/
theorem formerSortLoop_congr {R R' : CoreFnsA} (hW : R.whnf = R'.whnf) :
    ∀ (c d : Nat) (e : EIdx), formerSortLoop R d c e = formerSortLoop R' d c e := by
  intro c
  induction c with
  | zero => intro d e; simp only [formerSortLoop, hW]
  | succ c ih => intro d e; simp only [formerSortLoop, hW, ih]

/-- What `proj_guard_sort`'s refinement needs of a program. -/
structure PgsProg (p : Prog) : Prop extends FslProg p where
  pgs : p.lookup "proj_guard_sort" = some projGuardSortL
  pr : p.lookup "pi_result" = some piResultL
  frs : p.lookup "former_res_sort" = some formerResSortL
  laz : p.lookup "lv_always_zero" = some lvAlwaysZero
  pin : p.lookup "pin_word" = some pinWordL
  lvn : p.lookup "lv_never" = some lvNever
  prop : PropReadProg p
  ilp : InstLPOK p

section pgs
variable (p : Prog) (hp : PgsProg p)
include hp

/-- **`proj_guard_sort` refines `projGuardSort`, both outcomes**: the errors are
`former_sort_loop`'s (the `whnf` slot's) and the reject where no sort is reached. -/
theorem pgs_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (R : CoreFnsA)
    (hRW : R.whnf = (coreKnot (decMode mode) (decEager mode) fe id F).whnf)
    (m : Mem) (a : AState) (M : ModeMaps)
    (q us : Word) (cvT : IConstantVal) (caps : IIndCaps) (hS : CoreS dn m a vis fe M eb)
    (hci : decCI (erecP m) q.toNat = some (.indInfo cvT caps)) (hus : HW us) :
    RefE (KnotUpToE p n) (pgsE p (n + 1) m mode vis q us) (projGuardSort R cvT caps (decI us)) a
      (PgsPost dn m vis fe M eb) := by
  obtain ⟨hl, -, hty, hty32⟩ := decCV_rd (erRdOK m) (decCI_ind_cv' hci)
  obtain ⟨hni, hnp⟩ := decCI_ind_n (erRdOK m) hci
  simp only [erRd] at hl hty hty32 hni hnp
  rw [pgsE.eq_2]
  split
  · exact RefE.of_cls0 rfl
  rename_i hov
  have hn' := L.toNat_add_of_not_lt hov
  unfold ConRon.Arena.projGuardSort
  refine RefE.bindLift (fun _ => pgsE.k_former_res_sort.none ..) fun r1 m1 c1 => ?_
  obtain ⟨s1, hs1, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (frsV_spec p hp.frs n ⟨m, Locals.init []⟩ _) c1
  rw [hs1] at hW1
  obtain ⟨hm1, hrun1, hok1, hsv1⟩ := frsV_ok hp.pr hS.arena.base hty32 hW1
  clear hs1
  subst hm1
  refine ⟨_, _, by rw [hty]; exact hrun1, ?_⟩
  by_cases g1 : r1.headD 0 ≠ 0
  · rw [pgsE.k_former_res_sort.arm1 _ _ _ _ _ _ _ _ _ _ _ g1]
    simp only [decOS, show ¬ r1.headD 0 = 0 from g1, ↓reduceIte]
    obtain ⟨hh, hv⟩ := hsv1 g1
    obtain ⟨l, hdl⟩ := hS.den.sort _ _ hv
    obtain ⟨X, hX, hXok⟩ := readLevelM_run' _ _ l hdl hS.readL
    refine RefE.bind_right hX ?_
    have hS5 := hS.readLC' X hXok
    have hu : HW (r1.tail.headD 0) := hok1 g1
    rcases c5 : callW p n "lv_always_zero" [r1.tail.headD 0] m1 with _ | ⟨r5, m5⟩
    · rw [liftE_none, pgsE.k_lv_always_zero.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (lvAzW_spec p hp.laz n ⟨m1, Locals.init []⟩ _) c5
    rw [hs5] at hW5
    obtain ⟨hw5, hS6, hK6⟩ := lvAz_core (hp.prop.get "lv_node") (hp.prop.get "lh_push")
      (hp.prop.get "lv_zero") hS5 hu hdl hW5
    by_cases hz : l.isAlwaysZero = true
    · rw [pgsE.k_lv_always_zero.arm1 _ _ _ _ (by rw [hw5]; simp [hz])]
      simp only [hz, ↓reduceIte]
      rcases c6 : callW p n "pin_word" [53] m5 with _ | ⟨r6, m6⟩
      · rw [liftE_none, pgsE.k_pin_word.none]; exact RefE.of_cls0 (by simp)
      rw [liftE_some, pgsE.k_pin_word.arm1]
      obtain ⟨t6, ht6, hm6, -, hr6⟩ := triple_of_callW (pinWord_rd p hp.pin n ⟨m5, Locals.init []⟩ 53) c6
      have hm6' : m6 = m5 := ht6 ▸ hm6
      subst hm6'
      refine RefE.ret rfl ⟨⟨M, hS6, KeptAll.refl _ _, hK6⟩, by simp, ?_, .zero, ?_, rfl⟩
      · show HW (r6.headD 0)
        rw [hr6, ← pinW_rdW m6 53 53 rfl]; exact hS6.pins.lv_lt.2.1
      · show denoteL _ (decI (r6.headD 0)) = _
        rw [hr6]; exact zeroPin_den hS6
    · rw [pgsE.k_lv_always_zero.arm2 _ _ _ _ (by rw [hw5]; simp [hz])]
      simp only [hz, Bool.false_eq_true, ↓reduceIte]
      exact RefE.ret rfl ⟨⟨M, hS6, KeptAll.refl _ _, hK6⟩, rfl⟩
  have g1' : r1.headD 0 = 0 := by simpa using g1
  rw [pgsE.k_former_res_sort.arm2 _ _ _ _ _ _ _ _ _ _ _ g1']
  simp only [decOS, g1', ↓reduceIte]
  rw [hty]
  refine RefE.bind_callW (s₀ := ⟨m1, Locals.init []⟩) (fun _ => pgsE.k_inst_lp.none ..)
    (hp.ilp n ⟨m1, Locals.init []⟩ a dn vis fe M eb _ _ us _ cvT.levelParams hS hty32 hus hl)
    fun r3 m3 _ h3 => ?_
  obtain ⟨M3, hS3, hK3, hSt3⟩ := h3.after
  refine RefE.mono (R := PgsPost dn m3 vis fe M3 eb) ?_ (PgsPost.comp hK3 hSt3)
  rw [pgsE.k_inst_lp.arm1]; simp only [L.Ind.erRd_foldN]
  have hf := fsl_ref p hp.toFslProg n F hk hnF hn62 dn vis fe eb mode hm4 hebm n (by omega) m3 _ M3 0
    (erRd m1 (q + 17) + erRd m1 (q + 11)) (r3.headD 0) hS3 h3.resOk
  simp only [L.Ind.erRd_foldN] at hn' hni hnp
  rw [hn', ← hni, ← hnp, show ((0 : Word)).toNat = 0 from rfl,
    ← formerSortLoop_congr hRW] at hf
  rcases hx4 : fslE p n m3 mode vis 0 (erRd m1 (q + 17) + erRd m1 (q + 11)) (r3.headD 0) with
    e4 | ⟨r4, m4⟩
  · rw [hx4] at hf; rw [pgsE.k_former_sort_loop.none]
    exact RefE.bind_left fun hg => hf hg
  rw [hx4] at hf
  obtain ⟨y4, a4', hrun4', hP4⟩ := hf
  have h4 := hP4.coreRef hrun4'
  simp only [L.Ind.erRd_foldN] at h4
  refine RefE.bind_right (by rw [show decH r3 = decE (r3.headD 0) from rfl, AM.run_of_ok _ _ h4.run,
    h4.res]) ?_
  obtain ⟨M4, hS4, hK4, hSt4⟩ := h4.after
  refine RefE.mono (R := PgsPost dn m4 vis fe M4 eb) ?_ (PgsPost.comp hK4 hSt4)
  by_cases g4 : r4.headD 0 = 0
  · rw [pgsE.k_former_sort_loop.abort1 _ _ _ _ g4]
    simp only [decOS, g4, ↓reduceIte]
    exact fun _ => ErrClaim.of_error rfl rfl
  rw [pgsE.k_former_sort_loop.arm1 _ _ _ _ g4]
  simp only [decOS, g4, ↓reduceIte]
  have hu : HW (r4.tail.headD 0) := h4.resOk g4
  have hrun4 := AM.run_of_ok _ _ h4.run
  rw [h4.res] at hrun4
  rw [show decOS r4 = some (decI (r4.tail.headD 0)) by simp only [decOS, g4, ↓reduceIte]] at hrun4
  obtain ⟨hh, hvw⟩ := fsl_sortView _ _ _ _ _ _ _ hrun4
  obtain ⟨l, hdl⟩ := hS4.den.sort _ _ hvw
  obtain ⟨X, hX, hXok⟩ := readLevelM_run' _ _ l hdl hS4.readL
  refine RefE.bind_right hX ?_
  have hS5 := hS4.readLC' X hXok
  rcases c5 : callW p n "lv_never" [r4.tail.headD 0] m4 with _ | ⟨r5, m5⟩
  · rw [liftE_none, pgsE.k_lv_never.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (lvNeverW_spec p hp.lvn n ⟨m4, Locals.init []⟩ _) c5
  rw [hs5] at hW5
  obtain ⟨hw5, hS6, hK6⟩ := lvNever_core (hp.prop.get "lv_node") (hp.prop.get "lh_push")
    (hp.prop.get "lv_zero") hS5 hu hdl hW5
  by_cases hnv : (ConLeche.Level.zeronessOf l).isNever = true
  · rw [pgsE.k_lv_never.arm1 _ _ _ _ (by rw [hw5]; simp [hnv])]
    simp only [hnv, ↓reduceIte]
    exact RefE.ret rfl ⟨⟨M4, hS6, KeptAll.refl _ _, hK6⟩, rfl⟩
  · rw [pgsE.k_lv_never.arm2 _ _ _ _ (by rw [hw5]; simp [hnv])]
    simp only [hnv, Bool.false_eq_true, ↓reduceIte]
    exact RefE.ret rfl ⟨⟨M4, hS6, KeptAll.refl _ _, hK6⟩, by simp, hu, l, hdl, rfl⟩

end pgs

/-! ## The guard rows -/

/-- **A twin computation keeps every level handle's readback** (the store only grows). -/
def LKept {α : Type} (op : AM α) : Prop :=
  ∀ a x a', op.run a = .ok (x, a') →
    ∀ h l, denoteL a.store.ls h = some l → denoteL a'.store.ls h = some l

/-- **The knot's `whnf` and `infer_io` runs keep level readbacks** (the twin's store only grows
across them, `knot_smono`). -/
theorem knot_lkept (mode : ConLeche.CheckMode) (eager : Bool) (fe : IFEnv) (F d : Nat) (e : EIdx) :
    LKept ((coreKnot mode eager fe id F).whnf d e) ∧
      LKept ((coreKnot mode eager fe id F).inferIO d e) :=
  ⟨fun _ _ _ h hh l hd => (((knot_smono mode fe F eager).whnf d e).run h).ext.lss.ls.lvl hh l hd,
    fun _ _ _ h hh l hd => (((knot_smono mode fe F eager).inferIO d e).run h).ext.lss.ls.lvl hh l hd⟩

theorem GsDen.keep {a a' : AState} {gs : Word} {l : ConLeche.Level} (h : GsDen a gs l)
    (hk : ∀ h l, denoteL a.store.ls h = some l → denoteL a'.store.ls h = some l) : GsDen a' gs l :=
  let ⟨hw, l', hd, hz⟩ := h; ⟨hw, l', hk _ _ hd, hz⟩

theorem zeroWhereZero_congr {S S' U : ConLeche.Level}
    (h : ConLeche.Level.zeronessOf S = ConLeche.Level.zeronessOf S') :
    ConLeche.Level.zeroWhereZero S U = ConLeche.Level.zeroWhereZero S' U := by
  unfold ConLeche.Level.zeroWhereZero; rw [h]

section
variable {N : Word → ConLeche.Name → Prop}

/-- **`lh_contains`' loop is `List.contains`** on the names of the heap slice. -/
theorem lhcLoop_ok (hN : NameRel N) {m : Mem} {e w : Word} {nm : ConLeche.Name} (hw : N w nm) :
    ∀ (f : Nat) (j k : Word) (ps : List ConLeche.Name) (x : Word) (m' : Mem), NmsR N m LH j k ps →
      j.toNat + k.toNat < 2 ^ 64 → e = j + k → lhcW.loop1 f m e w j = some (x, m') →
      m' = m ∧ x = if ps.contains nm then 1 else 0 := by
  intro f
  induction f with
  | zero => intro j k ps x m' _ _ _ h; rw [lhcW.loop1.eq_1] at h; cases h
  | succ f ih =>
    intro j k ps x m' hps hov he h
    cases hps with
    | nil =>
      rw [lhcW.loop1.arm3 _ _ _ _ _ (by subst he; simp)] at h
      cases h; simp
    | @cons _ _ y ys hk hy hys =>
      have hk' : k.toNat ≠ 0 := fun h0 => hk (UInt64.toNat_inj.mp (by simpa using h0))
      have hlt : j < e := by
        subst he; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; rw [Nat.mod_eq_of_lt hov]; omega
      by_cases hr : rdW (m.arr64 LH) j = w
      · rw [lhcW.loop1.arm1 _ _ _ _ _ hlt hr] at h
        cases h
        rw [hr] at hy
        rw [hN.fn _ _ _ hy hw]; simp
      · rw [lhcW.loop1.arm2 _ _ _ _ _ hlt hr] at h
        have e1 : (j + 1).toNat = j.toNat + 1 := by
          rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
        have e2 : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        obtain ⟨rfl, hx⟩ := ih (j + 1) (k - 1) ys x m' hys (by rw [e1, e2]; omega)
          (by subst he; apply UInt64.toNat_inj.mp; simp only [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (show (1 : Word) ≤ k by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega) h
        refine ⟨rfl, ?_⟩
        have hne : y ≠ nm := fun h' => hr (hN.inj _ _ _ hy (h' ▸ hw))
        rw [hx]; simp [Ne.symm hne]

theorem lhc_call {p : Prog} (hp : p.lookup "lh_contains" = some lhContains) (hN : NameRel N)
    {n : Nat} {m m' : Mem} {t0 t1 w : Word} {r : List Word} {ps : List ConLeche.Name} {nm : ConLeche.Name}
    (hps : NmsR N m LH t0 (t1 - t0) ps) (hov : t0.toNat + (t1 - t0).toNat < 2 ^ 64)
    (he : t1 = t0 + (t1 - t0)) (hw : N w nm)
    (h : callW p n "lh_contains" [t0, t1, w] m = some (r, m')) :
    m' = m ∧ r.headD 0 = if ps.contains nm then 1 else 0 := by
  obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (lhcW_spec p hp n _ t0 t1 w) h
  rw [hs'] at hW
  rcases n with _ | n
  · rw [lhcW.eq_1] at hW; cases hW
  rw [lhcW.arm1] at hW
  exact lhcLoop_ok hN hw _ _ _ _ _ _ hps hov he hW

/-- **`lv_zero_where_zero`'s loop is `qs.all ps.contains`** (the top put back where it fails). -/
theorem zwzLoop_ok {p : Prog} (hp : p.lookup "lh_contains" = some lhContains) (hN : NameRel N)
    {m : Mem} {t0 t1 t2 : Word} {ps : List ConLeche.Name}
    (hps : NmsR N m LH t0 (t1 - t0) ps) (hov0 : t0.toNat + (t1 - t0).toNat < 2 ^ 64)
    (he0 : t1 = t0 + (t1 - t0)) :
    ∀ (f : Nat) (j k : Word) (qs : List ConLeche.Name) (sig : Sig) (m' : Mem), NmsR N m LH j k qs →
      j.toNat + k.toNat < 2 ^ 64 → t2 = j + k → lvZwzW.loop1 p f m t0 t1 t2 j = some (sig, m') →
      (qs.all ps.contains = true ∧ sig = .normal ∧ m' = m) ∨
        (qs.all ps.contains = false ∧ sig = .ret [0] ∧ m' = m.set64 CTL 192 t0) := by
  intro f
  induction f with
  | zero => intro j k qs sig m' _ _ _ h; rw [lvZwzW.loop1.eq_1] at h; cases h
  | succ f ih =>
    intro j k qs sig m' hqs hov he h
    rw [lvZwzW.loop1.eq_2] at h
    cases hqs with
    | nil =>
      rw [ite_eq_right (by subst he; simp)] at h
      cases h; simp
    | @cons _ _ y ys hk hy hys =>
      have hk' : k.toNat ≠ 0 := fun h0 => hk (UInt64.toNat_inj.mp (by simpa using h0))
      have hlt : j < t2 := by
        subst he; rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]; rw [Nat.mod_eq_of_lt hov]; omega
      rw [ite_eq_left hlt] at h
      rcases hc : callW p f "lh_contains" [t0, t1, rdW (m.arr64 LH) j] m with _ | ⟨r, m₁⟩
      · rw [hc, lvZwzW.k_lh_contains.none] at h; cases h
      rw [hc, lvZwzW.k_lh_contains.eq_def] at h
      simp only at h
      obtain ⟨rfl, hr⟩ := lhc_call hp hN hps hov0 he0 hy hc
      by_cases hy' : ps.contains y = true
      · rw [hr, ite_eq_left hy', ite_eq_right (by decide)] at h
        have e1 : (j + 1).toNat = j.toNat + 1 := by
          rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
        have e2 : (k - 1).toNat = k.toNat - 1 := by
          rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
        rcases ih (j + 1) (k - 1) ys sig m' hys (by rw [e1, e2]; omega)
          (by subst he; apply UInt64.toNat_inj.mp; simp only [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (show (1 : Word) ≤ k by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp; omega) h
          with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
        · exact .inl ⟨by rw [List.all_cons, hy', h1]; rfl, h2, h3⟩
        · exact .inr ⟨by rw [List.all_cons, hy', h1]; rfl, h2, h3⟩
      · rw [hr, ite_eq_right hy', ite_eq_left rfl] at h
        cases h
        have hf : ps.contains y = false := by simpa using hy'
        exact .inr ⟨by rw [List.all_cons, hf]; rfl, rfl, rfl⟩
end

/-- **`lv_zero_where_zero` is `Level.zeroWhereZero` under `CoreS`** (the heap top put back). -/
theorem lvZwz_core {p : Prog} (hpn : p.lookup "lv_node" = some lvNode)
    (hpp : p.lookup "lh_push" = some lhPush) (hpz : p.lookup "lv_zero" = some lvZero)
    (hpc : p.lookup "lh_contains" = some lhContains)
    {n : Nat} {dn : NIdx → Option ConLeche.Name} {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) {s u : Word} (hs : HW s) (hu : HW u)
    {S U : ConLeche.Level} (hdS : denoteL a.store.ls (decI s) = some S)
    (hdU : denoteL a.store.ls (decI u) = some U) {w : Word}
    (h : lvZwzW p n m s u = some (w, m')) :
    w = (if ConLeche.Level.zeroWhereZero S U then 1 else 0) ∧ CoreS dn m' a vis fe M eb ∧
      StackKept m m' := by
  rcases n with _ | n
  · simp [lvZwzW] at h
  have hN := nameN_rel _ hS.nwf
  rw [lvZwzW.arm1] at h
  rcases hc : callW p n "lv_zero" [s] m with _ | ⟨r₁, m₁⟩
  · rw [hc, lvZwzW.k_lv_zero.eq_1] at h; cases h
  rw [hc, lvZwzW.k_lv_zero.eq_2] at h
  obtain ⟨s₁, hs₁, -, hz₁⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m, Locals.init []⟩ s) hc
  rw [hs₁] at hz₁
  have hlS := denoteL_lvR hS.arena.base (decI s) S hdS
  rw [decI_word_self s hs] at hlS
  have hlU := denoteL_lvR hS.arena.base (decI u) U hdU
  rw [decI_word_self u hu] at hlU
  obtain ⟨he₁, hZ₁⟩ := zeroW_ok n _ _ _ _ _ hlS hz₁
  have hfin : ∀ m₂ : Mem, HeapExt m m₂ → m' = m₂.set64 CTL 192 (rdW (m.arr64 CTL) 192) →
      CoreS dn m' a vis fe M eb ∧ StackKept m m' := by
    intro m₂ he hm'
    subst hm'
    have hf : MemFrame [LH] [192] m (m₂.set64 CTL 192 (rdW (m.arr64 CTL) 192)) :=
      he.memFrame.trans ((MemFrame.setCtl m₂ 192 _).mono (by simp) (by simp))
    exact hS.frame hf (by simp [LH]) (by simp)
  unfold ConLeche.Level.zeroWhereZero
  by_cases h1 : r₁.headD 0 ≠ 0
  · rw [ite_eq_left h1] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hZ₁ with ⟨_, hx⟩ | ⟨hx, _⟩
    · rw [hx]; exact ⟨rfl, hfin m₁ he₁ rfl⟩
    · exact absurd hx h1
  rw [ite_eq_right h1] at h
  obtain ⟨ps, hpS, hps⟩ : ∃ ps, S.zeronessOf = .ifAllZero ps ∧
      NmsR (nameN a.store.lss.ls.ns) m₁ LH (htop m) (htop m₁ - htop m) ps := by
    rcases hZ₁ with ⟨hx, _⟩ | ⟨_, ps, h2, h3⟩
    · exact absurd hx (by simp only [ne_eq, Decidable.not_not] at h1; rw [h1]; decide)
    · exact ⟨ps, h2, h3⟩
  rcases hc2 : callW p n "lv_zero" [u] m₁ with _ | ⟨r₂, m₂⟩
  · rw [hc2, lvZwzW.k_lv_zero_2.eq_1] at h; cases h
  rw [hc2, lvZwzW.k_lv_zero_2.eq_2] at h
  obtain ⟨s₂, hs₂, -, hz₂⟩ := triple_of_callW (s₀ := ⟨m₁, Locals.init []⟩)
    (lvZero_spec p hpn hpp hpz n ⟨m₁, Locals.init []⟩ u) hc2
  rw [hs₂] at hz₂
  obtain ⟨he₂, hZ₂⟩ := zeroW_ok n _ _ _ _ _ (hlU.mono he₁) hz₂
  rw [hpS]
  have t₁ := he₁.top
  have t₂ := he₂.top
  by_cases h2 : r₂.headD 0 ≠ 0
  · rw [ite_eq_left h2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rcases hZ₂ with ⟨_, hx⟩ | ⟨hx, _⟩
    · rw [hx]; exact ⟨rfl, hfin m₂ (he₁.trans he₂) rfl⟩
    · exact absurd hx h2
  rw [ite_eq_right h2] at h
  obtain ⟨qs, hqU, hqs⟩ : ∃ qs, U.zeronessOf = .ifAllZero qs ∧
      NmsR (nameN a.store.lss.ls.ns) m₂ LH (htop m₁) (htop m₂ - htop m₁) qs := by
    rcases hZ₂ with ⟨hx, _⟩ | ⟨_, qs, h2, h3⟩
    · exact absurd hx (by simp only [ne_eq, Decidable.not_not] at h2; rw [h2]; decide)
    · exact ⟨qs, h2, h3⟩
  rw [hqU]
  have hd₁ : (htop m₁ - htop m).toNat = (htop m₁).toNat - (htop m).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  have hd₂ : (htop m₂ - htop m₁).toNat = (htop m₂).toNat - (htop m₁).toNat := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
  have hps₂ := hps.mono_lh he₂ (by rw [hd₁]; omega)
  have hlt0 := (htop m₁).toNat_lt
  have hlt2 := (htop m₂).toNat_lt
  rcases hl : lvZwzW.loop1 p (n + 1) m₂ (rdW (m.arr64 CTL) 192) (rdW (m₁.arr64 CTL) 192)
      (rdW (m₂.arr64 CTL) 192) (rdW (m₁.arr64 CTL) 192) with _ | ⟨sig, m₃⟩
  · rw [hl, lvZwzW.k_loop1.eq_1] at h; cases h
  rw [hl, lvZwzW.k_loop1.eq_2] at h
  rcases zwzLoop_ok hpc hN (t2 := htop m₂) hps₂ (by rw [hd₁]; omega)
      (by rw [UInt64.add_comm, UInt64.sub_add_cancel]) (n + 1) _ _ qs sig m₃ hqs (by rw [hd₂]; omega)
      (by rw [UInt64.add_comm, UInt64.sub_add_cancel]) hl with ⟨ha, hsg, hm3⟩ | ⟨ha, hsg, hm3⟩
  · subst hsg
    rw [hm3, ite_eq_left rfl] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [ha], hfin m₂ (he₁.trans he₂) rfl⟩
  · subst hsg
    rw [hm3, ite_eq_right (by simp)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨by simp [ha, Sig.retVal, Sig.retOr], hfin m₂ (he₁.trans he₂) rfl⟩

/-- **The guard rows on the stack**: row `i` at `ro + 2 i` (its depth) and `ro + 2 i + 1` (its
term). -/
def RowsAt (m : Mem) (ro : Word) (rows : Array (Nat × EIdx)) : Prop :=
  ∀ (i : Word) (h : i.toNat < rows.size), (spW m (ro + 2 * i)).toNat = (rows[i.toNat]'h).1 ∧
    HW (spW m (ro + 2 * i + 1)) ∧ decE (spW m (ro + 2 * i + 1)) = (rows[i.toNat]'h).2

theorem RowsAt.keep {m m' : Mem} {ro : Word} {rows : Array (Nat × EIdx)} (h : RowsAt m ro rows)
    (hb : ro.toNat + 2 * rows.size ≤ (spTop m).toNat)
    (hk : ∀ j, j < spTop m → spW m' j = spW m j) : RowsAt m' ro rows := by
  intro i hi
  have ht := (spTop m).toNat_lt
  have e1 : (ro + 2 * i).toNat = ro.toNat + 2 * i.toNat := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  have e2 : (ro + 2 * i + 1).toNat = ro.toNat + 2 * i.toNat + 1 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul]; simp; omega
  rw [hk _ (UInt64.lt_iff_toNat_lt.mpr (by omega)), hk _ (UInt64.lt_iff_toNat_lt.mpr (by omega))]
  exact h i hi

/-- What `check_guard_rows`' refinement needs of a program. -/
structure CgrProg (p : Prog) : Prop where
  cgr : p.lookup "check_guard_rows" = some checkGuardRowsL
  lzw : p.lookup "lv_zero_where_zero" = some lvZeroWhereZero
  lhc : p.lookup "lh_contains" = some lhContains
  prop : PropReadProg p

section cgr
variable (p : Prog) (hp : CgrProg p)
include hp

/-- **`check_guard_rows` refines `checkGuardRows`, both outcomes**, at every L fuel up to `n + 1`:
the errors are the `infer_io` and `whnf` slots', a type that is no sort, a row that is not a
proposition where the guard sort is zero. -/
theorem cgr_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (R : CoreFnsA)
    (hRW : R.whnf = (coreKnot (decMode mode) (decEager mode) fe id F).whnf)
    (hRI : R.inferIO = (coreKnot (decMode mode) (decEager mode) fe id F).inferIO)
    (gL : ConLeche.Level) (rows : Array (Nat × EIdx)) (ro rn : Word) (hrn : rows.size = rn.toNat) :
    ∀ (k : Nat), k ≤ n + 1 → ∀ (m : Mem) (a : AState) (M : ModeMaps) (i gs : Word),
      CoreS dn m a vis fe M eb → RowsAt m ro rows → ro.toNat + 2 * rows.size ≤ (spTop m).toNat →
      GsDen a gs gL →
      RefE (KnotUpToE p n) (cgrE p k m mode vis ro rn i gs) (checkGuardRows R gL rows i.toNat) a
        (CorePost (fun _ => ()) dn m vis fe M eb (fun _ => True)) := by
  intro k
  induction k with
  | zero => intro _ _ _ _ _ _ _ _ _ _; rw [cgrE.eq_def]; exact RefE.of_cls0 (by simp)
  | succ k ih =>
  intro hkn m a M i gs hS hR hb hG
  have hkn' : k ≤ n := by omega
  have hK := hk k hkn'
  have hs : SlotPre ⟨m, Locals.init []⟩ a dn vis fe M eb mode := ⟨hS, hm4, hebm⟩
  by_cases hi : rn ≤ i
  · rw [cgrE.arm1 _ _ _ _ _ _ _ _ _ hi]
    have : ¬ i.toNat < rows.size := by rw [hrn]; exact Nat.not_lt.mpr (UInt64.le_iff_toNat_le.mp hi)
    rw [checkGuardRows, dite_eq_right_iff.mpr (fun h => absurd h this)]
    exact RefE.ret rfl (CorePost.ret hS rfl trivial)
  rw [cgrE.arm2 _ _ _ _ _ _ _ _ _ hi]
  have hi' : i.toNat < rows.size := by rw [hrn]; exact UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hi)
  obtain ⟨hd, hdw, hdom⟩ := hR i hi'
  rw [checkGuardRows, dite_eq_left_of_eq_true (eq_true hi')]
  generalize hrow : rows[i.toNat] = row at hd hdom
  obtain ⟨d0, dom0⟩ := row
  simp only at hd hdom ⊢
  subst hd hdom
  rw [hRI]
  refine RefE.bind_callE (fun _ => cgrE.k_infer_io.none ..)
    (hK.inferIO F _ a dn vis fe M eb mode _ _ (by omega) (by omega) hs hdw)
    (fun hG => (hG k hkn').inferIO F _ a dn vis fe M eb mode _ _ (by omega) (by omega) hs hdw)
    fun r₁ m₁ _ h₁ => RefE.after_core (w := id) h₁ fun M₁ hS₁ hSt₁ => ?_
  rw [cgrE.k_infer_io.arm1, hRW]
  have hG₁ := hG.keep ((knot_lkept _ _ _ _ _ _).2 _ _ _ (AM.run_of_ok _ _ h₁.run))
  have hs₁ : SlotPre ⟨m₁, Locals.init []⟩ _ dn vis fe M₁ eb mode := ⟨hS₁, hm4, hebm⟩
  refine RefE.bind_callE (fun _ => cgrE.k_whnf.none ..)
    (hK.whnf F _ _ dn vis fe M₁ eb mode _ _ (by omega) (by omega) hs₁ h₁.resOk)
    (fun hG => (hG k hkn').whnf F _ _ dn vis fe M₁ eb mode _ _ (by omega) (by omega) hs₁ h₁.resOk)
    fun r₂ m₂ _ h₂ => RefE.after_core (w := id) h₂ fun M₂ hS₂ hSt₂ => ?_
  have hG₂ := hG₁.keep ((knot_lkept _ _ _ _ _ _).1 _ _ _ (AM.run_of_ok _ _ h₂.run))
  by_cases g1n : tagW (r₂.headD 0) ≠ 2
  · rw [cgrE.k_whnf.abort1 _ _ _ _ _ _ _ _ _ _ g1n]
    have g1 := g1n
    have ht : ¬ ((decH r₂).tag == ETag.sort) = true := by
      simp only [decH]; rw [decE_tag_sort_beq _ h₂.resOk]; simpa using g1
    simp only [ht, Bool.false_eq_true, ↓reduceIte]
    exact fun _ => ErrClaim.of_error rfl rfl
  have g1 : tagW (r₂.headD 0) = 2 := by simpa using g1n
  have ht : ((decH r₂).tag == ETag.sort) = true := by
    simp only [decH]; rw [decE_tag_sort_beq _ h₂.resOk]; simpa using g1
  simp only [ht, ↓reduceIte]
  by_cases g2 : tierW (r₂.headD 0) ≠ 0 ∧ rdW (m₂.arr64 CTL) 1 = 0
  · rw [cgrE.k_whnf.abort2 _ _ _ _ _ _ _ _ _ _ g1 g2]; exact RefE.of_cls0 rfl
  by_cases g3 : tcnt m₂ SORT (tierW (r₂.headD 0)) ≤ idxW (r₂.headD 0)
  · rw [cgrE.k_whnf.abort3 _ _ _ _ _ _ _ _ _ _ g1 g2 g3]; exact RefE.of_cls0 rfl
  rw [cgrE.k_whnf.arm1 _ _ _ _ _ _ _ _ _ _ g1 g2 g3]
  obtain ⟨hv, hu⟩ := L.Ind.view_sort_f m₂ _ hS₂.arena.base (r₂.headD 0) h₂.resOk
    ⟨g2, UInt64.not_le.mp g3⟩ g1
  have hvs := viewSort_of_view' _ _ _ (by
    have := decE_tag_sort_beq (e := r₂.headD 0) h₂.resOk; rw [g1] at this; simpa using this) hv
  refine RefE.bind_right (viewSort_run' hvs) ?_
  obtain ⟨l, hdl⟩ := hS₂.den.sort _ _ hv
  obtain ⟨X, hX, hXok⟩ := readLevelM_run' _ _ l hdl hS₂.readL
  refine RefE.bind_right hX ?_
  have hS₃ := hS₂.readLC' X hXok
  obtain ⟨hgs, L', hdL', hzL'⟩ := hG₂
  rcases c5 : callW p k "lv_zero_where_zero" [gs, tfld m₂ SORT (tierW (r₂.headD 0)) (idxW (r₂.headD 0)) 0] m₂
    with _ | ⟨r5, m5⟩
  · rw [liftE_none, cgrE.k_lv_zero_where_zero.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s5, hs5, -, hW5⟩ := triple_of_callW (s₀ := ⟨m₂, Locals.init []⟩)
    (lvZwzW_spec p hp.lzw k ⟨m₂, Locals.init []⟩ _ _) c5
  rw [hs5] at hW5
  obtain ⟨hw5, hS6, hK6⟩ := lvZwz_core (hp.prop.get "lv_node") (hp.prop.get "lh_push")
    (hp.prop.get "lv_zero") hp.lhc hS₃ hgs hu hdL' hdl hW5
  rw [zeroWhereZero_congr hzL'] at hw5
  by_cases hzn : ConLeche.Level.zeroWhereZero gL l = false
  · have hz := hzn
    rw [cgrE.k_lv_zero_where_zero.abort1 _ _ _ _ _ _ _ _ _ _ (by rw [hw5]; simp [hz])]
    simp only [hz, Bool.false_eq_true, ↓reduceIte]
    exact fun _ => ErrClaim.of_error rfl rfl
  have hz : ConLeche.Level.zeroWhereZero gL l = true := by simpa using hzn
  rw [cgrE.k_lv_zero_where_zero.arm1 _ _ _ _ _ _ _ _ _ _ (by rw [hw5]; simp [hz])]
  simp only [hz, ↓reduceIte]
  have hSt : StackKept m m5 := hSt₁.trans (hSt₂.trans hK6)
  have hi1 : (i + 1).toNat = i.toNat + 1 := by
    have := rn.toNat_lt; rw [UInt64.toNat_add]; simp only [UInt64.toNat_one]; omega
  have h1 := ih (by omega) m5 _ M₂ (i + 1) gs hS6 (hR.keep hb hSt.below) (by rw [hSt.top]; exact hb)
    ⟨hgs, L', hdL', hzL'⟩
  rw [hi1] at h1
  exact (RefE.tail_relist (g := fun r => [r.headD 0]) (fun _ => cgrE.k_check_guard_rows.none ..)
    (fun ⟨_, _⟩ => cgrE.k_check_guard_rows.arm1 ..) (fun _ => rfl) (fun _ _ => trivial) id h1).mono
    fun _ _ _ h => ⟨CoreAfter.comp (KeptAll.refl _ _) hK6 h.after, h.res, h.valid⟩

end cgr

/-! ## The record pool across the models -/

theorem coreFn_of {f : FnName} (h : coreFns.elem f = true) : f ∈ coreFns := List.elem_iff.mp h

/-- **A model step keeps the record pool's decoder view** when its callee's value does. -/
theorem ek_bind {K : Except Err (List Word × Mem) → Except Err (List Word × Mem)}
    (hK : ∀ e, K (.error e) = .error e) {x : Except Err (List Word × Mem)} {m m' : Mem}
    {r : List Word} (hx : ∀ r₁ m₁, x = .ok (r₁, m₁) → erecP m₁ = erecP m) (h : K x = .ok (r, m'))
    (hrest : ∀ r₁ m₁, x = .ok (r₁, m₁) → K (.ok (r₁, m₁)) = .ok (r, m') → erecP m' = erecP m₁) :
    erecP m' = erecP m := by
  rcases hx' : x with e | ⟨r₁, m₁⟩
  · rw [hx', hK] at h; cases h
  rw [hx'] at h; rw [hrest r₁ m₁ hx' h, hx r₁ m₁ hx']

theorem ek_W {p : Prog} (hE : ErecPKept p) {n : Nat} {f : FnName} {args : List Word} {m : Mem}
    (hf : f ∈ coreFns) : ∀ r₁ m₁, liftE (callW p n f args m) = .ok (r₁, m₁) → erecP m₁ = erecP m := by
  intro r₁ m₁ h
  rcases c : callW p n f args m with _ | ⟨r, m'⟩
  · rw [c, liftE_none] at h; cases h
  rw [c, liftE_some] at h; cases h; exact hE _ _ _ _ _ _ hf c

theorem ek_E {p : Prog} (hE : ErecPKept p) {n : Nat} {f : FnName} {args : List Word} {m : Mem}
    (hf : f ∈ coreFns) : ∀ r₁ m₁, callE p n f args m = .ok (r₁, m₁) → erecP m₁ = erecP m :=
  fun _ _ h => hE _ _ _ _ _ _ hf (callW_of_callE h)

theorem ek_ok {m₁ m' : Mem} {r r₁ : List Word} (h : (Except.ok (r₁, m₁) : Except Err _) = .ok (r, m')) :
    erecP m' = erecP m₁ := by cases h; rfl

set_option maxRecDepth 8192 in
theorem fslE_erec {p : Prog} (hE : ErecPKept p) : ∀ (k : Nat) (m : Mem) (mode vis d c e : Word)
    (r : List Word) (m' : Mem), fslE p k m mode vis d c e = .ok (r, m') → erecP m' = erecP m := by
  intro k
  induction k with
  | zero => intro m mode vis d c e r m' h; rw [fslE.eq_1] at h; cases h
  | succ k ih =>
    intro m mode vis d c e r m' h
    rw [fslE.eq_2] at h
    refine ek_bind (fun _ => fslE.k_whnf.none ..) (ek_E hE whnf_coreFn) h fun r₁ m₁ _ h => ?_
    rw [fslE.k_whnf.eq_2] at h
    split at h
    · split at h
      · exact ek_ok h
      split at h
      · cases h
      split at h
      · cases h
      exact ek_ok h
    split at h
    · exact ek_ok h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    refine ek_bind (fun _ => fslE.k_intern_fvar.none ..) (ek_W hE (coreFn_of (by decide))) h
      fun r₂ m₂ _ h => ?_
    rw [fslE.k_intern_fvar.arm1] at h
    refine ek_bind (fun _ => fslE.k_inst_entry.none ..) (ek_W hE (coreFn_of (by decide))) h
      fun r₃ m₃ _ h => ?_
    rw [fslE.k_inst_entry.eq_def] at h
    simp only at h
    refine ek_bind (fun _ => fslE.k_former_sort_loop.eq_1 ..) (fun _ _ h => ih _ _ _ _ _ _ _ _ h) h
      fun r₄ m₄ _ h => ?_
    rw [fslE.k_former_sort_loop.arm1] at h
    exact ek_ok h

set_option maxRecDepth 8192 in
theorem pgsE_erec {p : Prog} (hE : ErecPKept p) {k : Nat} {m : Mem} {mode vis q us : Word}
    {r : List Word} {m' : Mem} (h : pgsE p k m mode vis q us = .ok (r, m')) : erecP m' = erecP m := by
  rcases k with _ | k
  · rw [pgsE.eq_1] at h; cases h
  rw [pgsE.eq_2] at h
  split at h
  · cases h
  refine ek_bind (fun _ => pgsE.k_former_res_sort.none ..) (ek_W hE (coreFn_of (by decide))) h
    fun r₁ m₁ _ h => ?_
  rw [pgsE.k_former_res_sort.eq_2] at h
  split at h
  · refine ek_bind (fun _ => pgsE.k_lv_always_zero.none ..) (ek_W hE (coreFn_of (by decide))) h
      fun r₂ m₂ _ h => ?_
    rw [pgsE.k_lv_always_zero.eq_2] at h
    split at h
    · refine ek_bind (fun _ => pgsE.k_pin_word.none ..) (ek_W hE (coreFn_of (by decide))) h
        fun r₃ m₃ _ h => ?_
      rw [pgsE.k_pin_word.eq_2] at h; exact ek_ok h
    exact ek_ok h
  refine ek_bind (fun _ => pgsE.k_inst_lp.none ..) (ek_W hE (coreFn_of (by decide))) h
    fun r₂ m₂ _ h => ?_
  rw [pgsE.k_inst_lp.eq_2] at h
  refine ek_bind (fun _ => pgsE.k_former_sort_loop.none ..) (fun _ _ h => fslE_erec hE _ _ _ _ _ _ _ _ _ h) h
    fun r₃ m₃ _ h => ?_
  rw [pgsE.k_former_sort_loop.eq_2] at h
  split at h
  · cases h
  refine ek_bind (fun _ => pgsE.k_lv_never.none ..) (ek_W hE (coreFn_of (by decide))) h
    fun r₄ m₄ _ h => ?_
  rw [pgsE.k_lv_never.eq_2] at h
  split at h <;> exact ek_ok h

set_option maxRecDepth 8192 in
theorem cgrE_erec {p : Prog} (hE : ErecPKept p) : ∀ (k : Nat) (m : Mem) (mode vis ro rn i gs : Word)
    (r : List Word) (m' : Mem), cgrE p k m mode vis ro rn i gs = .ok (r, m') → erecP m' = erecP m := by
  intro k
  induction k with
  | zero => intro m mode vis ro rn i gs r m' h; rw [cgrE.eq_1] at h; cases h
  | succ k ih =>
    intro m mode vis ro rn i gs r m' h
    rw [cgrE.eq_2] at h
    split at h
    · exact ek_ok h
    refine ek_bind (fun _ => cgrE.k_infer_io.none ..) (ek_E hE inferIO_coreFn) h fun r₁ m₁ _ h => ?_
    rw [cgrE.k_infer_io.eq_2] at h
    refine ek_bind (fun _ => cgrE.k_whnf.none ..) (ek_E hE whnf_coreFn) h fun r₂ m₂ _ h => ?_
    rw [cgrE.k_whnf.eq_2] at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    refine ek_bind (fun _ => cgrE.k_lv_zero_where_zero.none ..) (ek_W hE (coreFn_of (by decide))) h
      fun r₃ m₃ _ h => ?_
    rw [cgrE.k_lv_zero_where_zero.eq_2] at h
    split at h
    · cases h
    refine ek_bind (fun _ => cgrE.k_check_guard_rows.none ..) (fun _ _ h => ih _ _ _ _ _ _ _ _ _ h) h
      fun r₄ m₄ _ h => ?_
    rw [cgrE.k_check_guard_rows.eq_2] at h; exact ek_ok h

set_option maxRecDepth 8192 in
theorem cpgE_erec {p : Prog} (hE : ErecPKept p) {k : Nat} {m : Mem} {mode vis q i us : Word}
    {r : List Word} {m' : Mem} (h : cpgE p k m mode vis q i us = .ok (r, m')) : erecP m' = erecP m := by
  rcases k with _ | k
  · rw [cpgE.eq_1] at h; cases h
  rw [cpgE.eq_2] at h
  refine ek_bind (fun _ => cpgE.k_env_find.none ..) (ek_W hE (coreFn_of (by decide))) h
    fun r₁ m₁ _ h => ?_
  rw [cpgE.k_env_find.eq_2] at h
  split at h
  · cases h
  split at h
  · cases h
  refine ek_bind (fun _ => cpgE.k_proj_guard_sort.none ..) (fun _ _ h => pgsE_erec hE h) h
    fun r₂ m₂ _ h => ?_
  rw [cpgE.k_proj_guard_sort.eq_2] at h
  split at h
  · exact ek_ok h
  refine ek_bind (fun _ => cpgE.k_proj_guard_rows.none ..) (ek_W hE (coreFn_of (by decide))) h
    fun r₃ m₃ _ h => ?_
  rw [cpgE.k_proj_guard_rows.eq_2] at h
  split at h
  · cases h
  refine ek_bind (fun _ => cpgE.k_check_guard_rows.none ..) (fun _ _ h => cgrE_erec hE _ _ _ _ _ _ _ _ _ _ h) h
    fun r₄ m₄ _ h => ?_
  rw [cpgE.k_check_guard_rows.eq_2] at h
  cases h
  exact erecP_frame (MemFrame.setCtl m₄ 136 _) (by simp) (by simp) (by simp) (by simp)

/-! ## `check_proj_guard` -/

/-- A table record's structure name (word `q + 2`). -/
theorem decTbl_sn {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {tbl : IProjTable} (h : decTbl R q.toNat = some tbl) :
    HW (rd (q + 2)) ∧ tbl.structName = decI (rd (q + 2)) := by
  unfold decTbl at h
  simp only [Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff, Option.some.injEq] at h
  obtain ⟨sn, hsn, _, _, _, _, _, _, _, _, _, _, rfl⟩ := h
  obtain ⟨w, hw, hw32, rfl⟩ := hd?_some hsn
  have e : rd (q + 2) = w := hR.offN (k := 2) hw (by decide)
  rw [e]
  exact ⟨hw32, rfl⟩

/-- **An inductive record's kind word** `3`. -/
theorem decCI_indF {R : Nat → Option Word} {rd : Word → Word} (hR : RdOK R rd) {q : Word}
    {ci : IConstantInfo} (h : decCI R q.toNat = some ci) :
    (rd q = 3 → ∃ cv caps, ci = .indInfo cv caps) ∧ (rd q ≠ 3 → ∀ cv caps, ci ≠ .indInfo cv caps) := by
  cases hq : R q.toNat with
  | none => simp [decCI, nat?, hq] at h
  | some w =>
  have hrd : rd q = w := hR.rd _ _ hq
  rw [hrd]
  simp only [decCI, nat?, hq, Option.map_some, Option.bind_eq_bind, Option.bind_some] at h
  constructor
  · intro hw; subst hw
    simp only [show UInt64.toNat 3 = 3 from rfl, Option.bind_eq_some_iff] at h
    obtain ⟨cv, -, caps, -, hc⟩ := h
    exact ⟨cv, caps, by simpa using hc.symm⟩
  · intro hw cv caps hc
    subst hc
    have hne : w.toNat ≠ 3 := fun e => hw (UInt64.toNat_inj.mp (by rw [e]; rfl))
    rcases hk : w.toNat with _ | _ | _ | _ | _ | _ | _ | k
    all_goals (rw [hk] at h hne; simp [Option.bind_eq_some_iff] at h hne)

/-- `proj_guard_rows`' words against `projGuardRows`' answer, run from `m₀` to `m`: `(0, _, _)`
none; `(1, ro, rn)` the rows at the old top `ro`, below the new top. -/
def PgrRes (m₀ m : Mem) (r : List Word) : Option (Array (Nat × EIdx)) → Prop
  | none => r.headD 0 = 0
  | some rows => r.headD 0 ≠ 0 ∧ r.tail.headD 0 = spTop m₀ ∧
      rows.size = (r.tail.tail.headD 0).toNat ∧ RowsAt m (spTop m₀) rows ∧
      (spTop m₀).toNat + 2 * rows.size ≤ (spTop m).toNat

/-- **`proj_guard_rows` refines `projGuardRows`** (no slot reached: its lifted run): the rows left
on the stack above the old top, the twin's level readbacks kept. -/
def PgrOK (p : Prog) : Prop :=
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (m m' : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb q i us : Word) (tbl : IProjTable) (r : List Word),
    CoreS dn m a vis fe M eb → decTbl (erecP m) q.toNat = some tbl → (∃ c, fe.findTable? c = some tbl) →
    HW us → callW p n "proj_guard_rows" [vis, q, i, us] m = some (r, m') →
    ∃ y a', (projGuardRows fe (tbl.entry i.toNat) (decI us)).run a = .ok (y, a') ∧
      CoreAfterG dn m m' a' vis fe M eb ∧
      (∀ h l, denoteL a.store.ls h = some l → denoteL a'.store.ls h = some l) ∧ PgrRes m m' r y ∧
      L.Ind.IWOK m' ∧ L.Ind.IWGrow m m' ∧ ∃ mp, L.Ind.hbMR m' mp

/-- What `check_proj_guard`'s refinement needs of a program. -/
structure CpgProg (p : Prog) : Prop extends PgsProg p where
  cgrP : CgrProg p
  cpg : p.lookup "check_proj_guard" = some checkProjGuardL
  envFind : p.lookup "env_find" = some envFindL
  envRowGet : p.lookup "env_row_get" = some envRowGetL
  baseRowGet : p.lookup "base_row_get" = some baseRowGetL

theorem RefE.mapG {α β : Type} {G G' : Prop} {x : Except Err α} {T : AM β} {a : AState}
    {R : α → β → AState → Prop} (hG : G → G') (h : RefE G' x T a R) : RefE G x T a R := by
  cases x with
  | ok v => exact h
  | error e => exact fun g => h (hG g)

section cpg
variable (p : Prog) (hp : CpgProg p) (hpg : PgrOK p) (hE : ErecPKept p)
include hp hpg hE

/-- **`check_proj_guard` refines `checkProjGuard`, both outcomes**: the structure's record, the
guard sort (`pgs_ref`), the rows (`PgrOK`), each row (`cgr_ref`); the stack top put back. -/
theorem cpg_ref (n F : Nat) (hk : KnotUpTo p n) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode : Word)
    (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (R : CoreFnsA)
    (hRW : R.whnf = (coreKnot (decMode mode) (decEager mode) fe id F).whnf)
    (hRI : R.inferIO = (coreKnot (decMode mode) (decEager mode) fe id F).inferIO)
    (m : Mem) (a : AState) (M : ModeMaps) (q i us : Word) (tbl : IProjTable)
    (hS : CoreS dn m a vis fe M eb) (hq : decTbl (erecP m) q.toNat = some tbl)
    (hfe : ∃ c, fe.findTable? c = some tbl) (hus : HW us) :
    RefE (KnotUpToE p n) (cpgE p (n + 1) m mode vis q i us)
      (checkProjGuard R fe (tbl.entry i.toNat) (decI us)) a
      (CorePost (fun _ => ()) dn m vis fe M eb (fun _ => True)) := by
  obtain ⟨hsn, hsnd⟩ := decTbl_sn (erRdOK m) hq
  simp only [erRd] at hsn hsnd
  unfold ConRon.Arena.checkProjGuard
  rw [cpgE.eq_2]
  have hsn' : (tbl.entry i.toNat).structName = tbl.structName := rfl
  rw [hsn', hsnd]
  rcases c1 : callW p n "env_find" [rdW (m.arr64 (tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775), vis] m
    with _ | ⟨r1, m1⟩
  · rw [liftE_none, cpgE.k_env_find.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s1, hs1, hm1, -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hp.envRowGet hp.baseRowGet hp.envFind n _ vis _ hS.env hsn) c1
  have hm1' : m1 = m := hs1 ▸ hm1
  subst hm1'
  by_cases g1 : r1.headD 0 = 0
  · rw [cpgE.k_env_find.eq_2, ite_eq_left g1]
    have : fe.find? (decI (rdW (m1.arr64 (tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775))) = none := by
      rw [hfind]; simp only [envFound, g1, ↓reduceIte]
    rw [this]; exact fun _ => ErrClaim.of_error rfl rfl
  obtain ⟨ci, hci⟩ := hdec g1
  have hfind' : fe.find? (decI (rdW (m1.arr64 (tierA EREC ((q + 2) >>> 40))) (q + 2 &&& 1099511627775))) =
      some ci := by rw [hfind]; simp only [envFound, g1, ↓reduceIte]; exact hci
  rw [hfind']
  have hK := decCI_indF (erRdOK m1) hci
  simp only [erRd] at hK
  by_cases g2n : rdW (m1.arr64 (tierA EREC (r1.tail.headD 0 >>> 40))) (r1.tail.headD 0 &&& 1099511627775) ≠ 3
  · have g2 := g2n
    rw [cpgE.k_env_find.eq_2, ite_eq_right g1, ite_eq_left g2]
    rcases ci with _ | _ | _ | ⟨cvT, caps⟩ | _ | _
    all_goals first
      | exact absurd rfl (hK.2 g2 _ _)
      | exact fun _ => ErrClaim.of_error rfl rfl
  have g2 : rdW (m1.arr64 (tierA EREC (r1.tail.headD 0 >>> 40))) (r1.tail.headD 0 &&& 1099511627775) = 3 := by
    simpa using g2n
  obtain ⟨cvT, caps, rfl⟩ := hK.1 g2
  rw [cpgE.k_env_find.eq_2, ite_eq_right g1, ite_eq_right g2n]
  rcases n with _ | n
  · rw [pgsE.eq_1, cpgE.k_proj_guard_sort.none]; exact RefE.of_cls0 (by simp)
  have hpgs := pgs_ref p hp.toPgsProg n F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb
    mode hm4 hebm R hRW m1 a M (r1.tail.headD 0) us cvT caps hS hci hus
  simp only
  rcases hx2 : pgsE p (n + 1) m1 mode vis (r1.tail.headD 0) us with e2 | ⟨r2, m2⟩
  · rw [hx2] at hpgs; rw [cpgE.k_proj_guard_sort.none]
    exact RefE.bind_left fun hg => hpgs (hg.mono (Nat.le_succ _))
  rw [hx2] at hpgs
  obtain ⟨y2, a2, hrun2, hP2⟩ := hpgs
  refine RefE.bind_right hrun2 ?_
  obtain ⟨M2, hS2, hK2, hSt2⟩ := hP2.after
  have he2 : erecP m2 = erecP m1 := pgsE_erec hE hx2
  have hres2 := hP2.res
  rcases y2 with _ | gL
  · have g : r2.headD 0 = 0 := hres2
    rw [cpgE.k_proj_guard_sort.eq_2, ite_eq_left g]
    exact RefE.ret rfl ⟨⟨M2, hS2, hK2, hSt2⟩, rfl, trivial⟩
  obtain ⟨g3, hgs⟩ := hres2
  rw [cpgE.k_proj_guard_sort.eq_2, ite_eq_right g3]
  simp only
  rcases c3 : callW p (n + 1) "proj_guard_rows" [vis, q, i, us] m2 with _ | ⟨r3, m3⟩
  · rw [liftE_none, cpgE.k_proj_guard_rows.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨y3, a3, hrun3, hA3, hL3, hres3, -⟩ := hpg _ dn m2 m3 a2 vis fe M2 eb q i us tbl r3 hS2
    (by rw [he2]; exact hq) hfe hus c3
  refine RefE.bind_right hrun3 ?_
  obtain ⟨M3, hS3, hK3, hG3⟩ := hA3
  rcases y3 with _ | rows
  · have g : r3.headD 0 = 0 := hres3
    rw [cpgE.k_proj_guard_rows.eq_2, ite_eq_left g]
    exact fun _ => ErrClaim.of_error rfl rfl
  obtain ⟨g4, hro, hsz, hrows, hb⟩ := hres3
  rw [cpgE.k_proj_guard_rows.eq_2, ite_eq_right g4, hro]
  simp only
  have hc := cgr_ref p hp.cgrP n F (hk.mono (Nat.le_succ _)) (by omega) (by omega) dn vis fe eb mode hm4 hebm
    R hRW hRI gL rows (spTop m2) (r3.tail.tail.headD 0) hsz (n + 1) (Nat.le_refl _) m3 a3 M3 0 _ hS3 hrows hb
    (hgs.keep hL3)
  refine RefE.tail_eq (k := cpgE.k_check_guard_rows p (rdW (m1.arr64 CTL) 136))
    (f := fun v => ([0], v.2.set64 CTL 136 (rdW (m1.arr64 CTL) 136)))
    (fun _ => cpgE.k_check_guard_rows.none ..) (fun ⟨_, _⟩ => cpgE.k_check_guard_rows.eq_2 ..)
    (fun hg => hg.mono (Nat.le_succ _)) rfl ?_ hc
  intro v y a' h
  obtain ⟨M5, hS5, hK5, hSt5⟩ := h.after
  have hg : StackGrew m1 v.2 := hSt2.toGrew.trans (hG3.trans hSt5.toGrew)
  exact ⟨⟨M5, hS5.frame_stk (MemFrame.setCtl _ 136 _) (by simp) (by simp), hK2.trans (hK3.trans hK5),
    StackKept.restoreG' hg⟩, rfl, trivial⟩

end cpg

end L.Arena
