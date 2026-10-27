import ConAgua.Arena.WhnfIotaRefine3
import ConAgua.Arena.CoreLevels
import ConAgua.Arena.CoreDen
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 4 (`proof_irrel`, `prepare_major`, …)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem view_sort_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h SORT) (hg : h >>> 28 = 2) :
    a.store.view (decE h) = some (.sort (decI (tfld m SORT (tierW h) (idxW h) 0))) ∧
    (tfld m SORT (tierW h) (idxW h) 0).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hu⟩ := node_of m a h sortCS SoRecRel (·.sorts) _ hR.sort hv.2
  simp only [SoRecRel] at hu
  rw [hu, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_sort _ h hh hg, Tbl.node?, hk]; rfl, word_lt _⟩

/-! ## `proof_irrel(mode, vis, d, a, b)` -/

/-- Model of `proof_irrel_half`. -/
def pihW (p : Prog) (n : Nat) (m : Mem) (mode vis d x : Word) : Option (Word × Mem) :=
  match callW p n "infer_io" [mode, vis, d, x] m with
  | none => none
  | some (r1, m1) =>
  match callW p n "infer_io" [mode, vis, d, r1.headD 0] m1 with
  | none => none
  | some (r2, m2) =>
  match callW p n "whnf" [mode, vis, d, r2.headD 0] m2 with
  | none => none
  | some (r3, m3) =>
  if r3.headD 0 >>> 28 ≠ 2 then some (0, m3)
  else if tierW (r3.headD 0) ≠ 0 ∧ rdW (m3.arr64 CTL) 1 = 0 then none
  else if tcnt m3 SORT (tierW (r3.headD 0)) ≤ idxW (r3.headD 0) then none
  else
  match callW p n "pin_word" [53] m3 with
  | none => none
  | some (z, m4) =>
  match callW p n "lvl_eq_c"
      [tfld m3 SORT (tierW (r3.headD 0)) (idxW (r3.headD 0)) 0, z.headD 0] m4 with
  | none => none
  | some (ok, m5) => if ok.headD 0 = 0 then none else some (ok.headD 0, m5)

theorem proofIrrelHalf_spec (p : Prog) (hp : p.lookup "proof_irrel_half" = some proofIrrelHalfL)
    (n : Nat) (s₀ : St) (mode vis d x : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "proof_irrel_half" [mode, vis, d, x]
    ⦃fun r s' => LocEq s' s₀ ∧ pihW p n s₀.mem mode vis d x = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, proofIrrelHalfL]
  sym only [lang_grind, arena_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, evalE_tld, tld, evalE_cnt,
      tcntM, evalE_tierE, evalE_idxE,
      callW_spec p n "infer_io", callW_spec p n "whnf", callW_spec p n "pin_word",
      callW_spec p n "lvl_eq_c"] <;>
    finish [pihW, tierW, idxW]

/-- Model of `proof_irrel`. -/
def pirrW (p : Prog) (n : Nat) (m : Mem) (mode vis d a b : Word) : Option (List Word × Mem) :=
  match callW p n "proof_irrel_half" [mode, vis, d, a] m with
  | none => none
  | some (ra, m1) =>
  if ra.headD 0 = 0 then some ([0], m1) else
  match callW p n "proof_irrel_half" [mode, vis, d, b] m1 with
  | none => none
  | some (rb, m2) =>
  if rb.headD 0 = 0 then some ([0], m2) else
  some ([(if ra.headD 0 = 1 then 0 else 1) &&& (if rb.headD 0 = 1 then 0 else 1)], m2)

theorem proofIrrel_spec (p : Prog) (hp : p.lookup "proof_irrel" = some proofIrrelL) (n : Nat)
    (s₀ : St) (mode vis d a b : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "proof_irrel" [mode, vis, d, a, b]
    ⦃fun r s' => LocEq s' s₀ ∧ pirrW p n s₀.mem mode vis d a b = some ([r.headD 0], s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, proofIrrelL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "proof_irrel_half"] <;>
  simp_all [pirrW, Cmp.eval, Cmp.evalW, BinOp.eval, LocEq, St.setLocs_cons, St.setLoc_loc,
    St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal,
    Sig.retOr]


/-! ### The refinement -/

/-- **Program hypotheses of part 4**: part 3's, the level cache's, and `pin_word`. -/
structure IotaProg4 (p : Prog) : Prop extends IotaProg' p where
  lvl : LvlCacheProg p
  pinw : p.lookup "pin_word" = some pinWordL

/-- A `sort` node of the store has a level that reads back (`denoteL` is defined at its handle),
and so does the pinned zero level: `CoreS.den` (`StoreDen.lean`, lane `defeq2`). `lvl_eq_c` (lane
`levels`/`CoreLevels.lean`'s `lvlEqC_refines`) needs this, the twin's `readLevelM` fails on a
dangling handle. -/
theorem CoreS.lvl_den {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) :
    (∀ (e : EIdx) (u : LIdx), a.store.view e = some (.sort u) → ∃ l, denoteL a.store.ls u = some l) ∧
    (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l) :=
  ⟨fun e u hv => hS.den.sort e u hv, hS.den.zero⟩

/-- **What `proof_irrel` needs of the store** (`CoreS.lvl_den`'s statement, as a named
hypothesis): a `sort` node's level and the pinned zero level read back. -/
def LvlDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb →
    (∀ (e : EIdx) (u : LIdx), a.store.view e = some (.sort u) → ∃ l, denoteL a.store.ls u = some l) ∧
    (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l)

/-- `LvlDen` from `CoreDen` (`StoreDen.sort`, `StoreDen.zero`). -/
theorem LvlDen.of_den (h : CoreDen) : LvlDen :=
  fun dn m a vis fe M eb hS => ⟨(h dn m a vis fe M eb hS).sort, (h dn m a vis fe M eb hS).zero⟩

/-- `lvl_eq_c` cannot run on fuel below two. -/
theorem lvlEqC_small (p : Prog) (hp : p.lookup "lvl_eq_c" = some lvlEqCL) (n : Nat) (hn : n < 2)
    (vs : List Word) (m : Mem) : callW p n "lvl_eq_c" vs m = none := by
  rcases Nat.lt_or_ge n 1 with h0 | h1
  · have : n = 0 := by omega
    subst this; exact callW_zero _ _ _ _
  · have : n = 1 := by omega
    subst this
    cases hc : callW p 1 "lvl_eq_c" vs m with
    | none => rfl
    | some q =>
      exfalso
      obtain ⟨t, -, hF⟩ := triple_of_callW (p := p) (n := 1) (f := "lvl_eq_c") (args := vs)
        (s₀ := ⟨m, Locals.init []⟩) (Q := fun _ _ => False) (by
          rw [invoke_eq _ hp]
          simp only [callFn, lvlEqCL]
          vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
            callW_spec p 0 "lq_find", callW_spec p 0 "lvl_eq_rec"] <;>
          simp_all [callW_zero]) hc
      exact hF

/-- The twin's half of `proofIrrel` (for the proof): `w = 0` the head is not a sort, else the
comparison's verdict (`w = 2` true). -/
def PiHalfRun (r : CoreFnsA) (d : Nat) (x : EIdx) (a : AState) (w : Word) (a' : AState) : Prop :=
  ∃ (ta tta hh : EIdx) (a1 a2 a3 : AState),
    (r.inferIO d x).run a = .ok (ta, a1) ∧ (r.inferIO d ta).run a1 = .ok (tta, a2) ∧
    (r.whnf d tta).run a2 = .ok (hh, a3) ∧
    ((w = 0 ∧ hh.tag ≠ ETag.sort ∧ a' = a3) ∨
     (w ≠ 0 ∧ hh.tag = ETag.sort ∧ ∃ (uT z : LIdx) (a4 : AState),
        a3.store.view hh = some (.sort uT) ∧ zeroLevel.run a3 = .ok (z, a3) ∧
        (lvlEq? uT z).run a3 = .ok (some (decide (w ≠ 1)), a4) ∧ a' = a4))

theorem proofIrrel_run_none (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a b : EIdx) (s s' : AState)
    (h : PiHalfRun r d a s 0 s') :
    (proofIrrel r fe d a b).run s = .ok (false, s') := by
  obtain ⟨ta, tta, hh, a1, a2, a3, h1, h2, h3, h4⟩ := h
  rcases h4 with ⟨-, ht, rfl⟩ | ⟨hne, -⟩
  · simp only [proofIrrel, StateT.run_bind, h1, h2, h3, except_ok_bind]
    have : (hh.tag == ETag.sort) = false := by simpa using ht
    simp [this]; rfl
  · exact absurd rfl hne

theorem proofIrrel_run_half (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a b : EIdx) (s s1 s2 : AState)
    (wa wb : Word) (hwa : wa ≠ 0) (ha : PiHalfRun r d a s wa s1) (hb : PiHalfRun r d b s1 wb s2) :
    (proofIrrel r fe d a b).run s = .ok (decide (wa ≠ 1) && decide (wb ≠ 0 ∧ wb ≠ 1), s2) := by
  obtain ⟨ta, tta, hh, a1, a2, a3, h1, h2, h3, h4⟩ := ha
  rcases h4 with ⟨h0, -⟩ | ⟨-, ht, uT, z, a4, hv, hz, hl, hs1⟩
  · exact absurd h0 hwa
  obtain ⟨tb, ttb, hh', b1, b2, b3, g1, g2, g3, g4⟩ := hb
  subst hs1
  have hv' : (view hh).run a3 = .ok (.sort uT, a3) := by
    simp [view, hv, StateT.run_bind, StateT.run_get]; rfl
  have hl' : (liftFueled "level comparison" (some (decide (wa ≠ 1)))).run s1 = .ok (decide (wa ≠ 1), s1) := by
    simp [liftFueled]; rfl
  simp only [proofIrrel, StateT.run_bind, h1, h2, h3, except_ok_bind, ht, beq_self_eq_true, ↓reduceIte,
    hv', hz, hl, hl']
  rcases g4 with ⟨h0, gt, rfl⟩ | ⟨hwb, gt, uT', z', b4, gv, gz, gl, rfl⟩
  · have : (hh'.tag == ETag.sort) = false := by simpa using gt
    simp only [g1, g2, g3, except_ok_bind, this]
    subst h0
    simp; rfl
  · have gv' : (view hh').run b3 = .ok (.sort uT', b3) := by
      simp [view, gv, StateT.run_bind, StateT.run_get]; rfl
    have gl' : (liftFueled "level comparison" (some (decide (wb ≠ 1)))).run s2 =
        .ok (decide (wb ≠ 1), s2) := by
      simp [liftFueled]; rfl
    simp only [StateT.run_bind, g1, g2, g3, except_ok_bind, gt, beq_self_eq_true, ↓reduceIte,
      gv', gz, gl, gl']
    simp [hwb]; rfl


/-- Model of `pin_word`. -/
def pinWordM (m : Mem) (k : Word) : Option (List Word × Mem) :=
  if pinW m 0 = 0 then none else some ([rdW (m.arr64 PINS) k], m)

theorem pinWord_specM (p : Prog) (hp : p.lookup "pin_word" = some pinWordL) (n : Nat) (s₀ : St)
    (k : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "pin_word" [k]
    ⦃fun r s' => LocEq s' s₀ ∧ pinWordM s₀.mem k = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, pinWordL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinWordM, pinW_eq, rdW_eq]

theorem pihW_ok (p : Prog) (hp : IotaProg4 p) (hld : LvlDen) (n F : Nat) (hknot : KnotUpTo p n) (hnF : n ≤ F)
    (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d x : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hx : HW x)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (w : Word) (m' : Mem)
    (h : pihW p n m mode vis d x = some (w, m')) :
    ∃ a', PiHalfRun (coreKnot (decMode mode) fe id F) d.toNat (decE x) a w a' ∧
      CoreAfter dn m m' a' vis fe M eb ∧ HW w := by
  simp only [pihW] at h
  rcases c1 : callW p n "infer_io" [mode, vis, d, x] m with _ | ⟨r1, m1⟩ <;>
    simp only [c1, reduceCtorEq] at h
  obtain ⟨hrun1, ⟨M1, hS1, hK1, hSt1⟩, hr1⟩ := CoreSpec.run
    ((hknot n (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d x hnF hn62
      ⟨hS, hm4, hebm⟩ hx) c1
  rcases c2 : callW p n "infer_io" [mode, vis, d, r1.headD 0] m1 with _ | ⟨r2, m2⟩ <;>
    simp only [c2, reduceCtorEq] at h
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
    ((hknot n (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _ hnF hn62
      ⟨hS1, hm4, hebm⟩ hr1) c2
  rcases c3 : callW p n "whnf" [mode, vis, d, r2.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
    simp only [c3, reduceCtorEq] at h
  obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, hr3⟩ := CoreSpec.run
    ((hknot n (Nat.le_refl _)).whnf F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ hnF hn62
      ⟨hS2, hm4, hebm⟩ hr2) c3
  have hKA : KeptAll M M3 eb := hK1.trans (hK2.trans hK3)
  have hStA : StackKept m m3 := hSt1.trans (hSt2.trans hSt3)
  by_cases h2 : r3.headD 0 >>> 28 ≠ 2
  · rw [ite_eq_left h2] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    refine ⟨_, ⟨_, _, _, _, _, _, hrun1, hrun2, hrun3, Or.inl ⟨rfl, ?_, rfl⟩⟩,
      ⟨M3, hS3, hKA, hStA⟩, by unfold HW; decide⟩
    exact fun ht => h2 ((decE_tag_eq _ hr3 2 (by decide)).mp ht)
  rw [ite_eq_right h2] at h
  have h2' : r3.headD 0 >>> 28 = 2 := by simpa using h2
  obtain ⟨hv1, h⟩ := of_ite_none h
  obtain ⟨hv2, h⟩ := of_ite_none h
  obtain ⟨hvw, hn32⟩ := view_sort_f m3 (AM.st _ _) hS3.arena.1 (r3.headD 0) hr3
    ⟨hv1, UInt64.not_le.mp hv2⟩ h2'
  generalize tfld m3 SORT (tierW (r3.headD 0)) (idxW (r3.headD 0)) 0 = uw at hvw hn32 h
  rcases c4 : callW p n "pin_word" [53] m3 with _ | ⟨r4, m4⟩ <;> simp only [c4, reduceCtorEq] at h
  obtain ⟨t4, ht4, hloc4, hpw⟩ := triple_of_callW
    (pinWord_specM p hp.pinw n ⟨m3, Locals.init []⟩ 53) c4
  have hpw' : pinWordM m3 53 = some (r4, m4) := by simpa [ht4] using hpw
  obtain ⟨-, hpw'⟩ := of_ite_none hpw'
  obtain ⟨hr4, rfl⟩ := Prod.mk.inj (Option.some.inj hpw')
  have hP := hS3.pins
  have hr4' : r4.headD 0 = pinW m3 53 := by
    rw [← hr4]; simp [rdW, pinW]
  obtain ⟨a3, ha3⟩ : ∃ a3, a3 = AM.st ((coreKnot (decMode mode) fe id F).whnf d.toNat
      (decE (r2.headD 0))) (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat
      (decE (r1.headD 0))) (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE x)) a)) :=
    ⟨_, rfl⟩
  rw [← ha3] at hrun3 hvw hS3 hP
  rcases Nat.lt_or_ge n 2 with hsm | hbig
  · rw [lvlEqC_small p hp.lvl.c n hsm] at h; cases h
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  rcases c5 : callW p (n' + 2) "lvl_eq_c" [uw, r4.headD 0] m3 with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at h
  obtain ⟨hdn1, hdn2⟩ := hld _ _ _ _ _ _ _ hS3
  obtain ⟨lu, hdu⟩ := hdn1 _ _ hvw
  have hzl : a3.pins.zeroLevel = decI (r4.headD 0) := by rw [hP.zeroLevel, hr4']
  obtain ⟨lz, hdz⟩ := hdn2
  rw [hzl] at hdz
  have hz32 : HW (r4.headD 0) := by rw [hr4']; exact hP.lv_lt.2.1
  obtain ⟨hrunL, ⟨M5, hS5, hK5, hSt5⟩, hr5⟩ := CoreSpec.run
    (lvlEqC_refines p hp.lvl n' ⟨m3, Locals.init []⟩ a3 dn vis fe M3 eb hS3 uw (r4.headD 0)
      hn32 hz32 lu lz hdu hdz) c5
  obtain ⟨hw0, h⟩ := of_ite_none h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hdec : ∀ v : Word, v ≠ 0 → decO v = some (decide (v ≠ 1)) := by
    intro v hv; unfold decO; by_cases h1 : v = 1 <;> simp [hv, h1]
  simp only [hdec _ hw0] at hrunL
  have hz : zeroLevel.run a3 = .ok (decI (r4.headD 0), a3) := by
    rw [hr4']; exact pinZeroLevel_run hP
  have htag : (decE (r3.headD 0)).tag = ETag.sort := (decE_tag_eq _ hr3 2 (by decide)).mpr h2'
  have hrun3' : (((coreKnot (decMode mode) fe id F).whnf d.toNat (decE (r2.headD 0))).run
      (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE (r1.headD 0)))
        (AM.st ((coreKnot (decMode mode) fe id F).inferIO d.toNat (decE x)) a))) =
      .ok (decE (r3.headD 0), a3) := hrun3
  exact ⟨_, ⟨_, _, _, _, _, a3, hrun1, hrun2, hrun3', Or.inr ⟨hw0, htag, decI uw, decI (r4.headD 0), _,
    hvw, hz, hrunL, rfl⟩⟩, ⟨M5, hS5, hKA.trans hK5, hStA.trans hSt5⟩, hr5⟩


/-- `proofIrrel_refines` over the named hypothesis `LvlDen` (`LvlDen.of_den` from `CoreDen`). -/
theorem proofIrrel_refines' (p : Prog) (hp : IotaProg4 p) (hld : LvlDen) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d a b hS hm4 hebm ha hb
  refine triple_post (proofIrrel_spec p hp.proofIrrel n s₀ mode vis d a b) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  simp only [pirrW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ n' =>
  rcases c1 : callW p (n' + 1) "proof_irrel_half" [mode, vis, d, a] s₀.mem with _ | ⟨ra, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, -, hpa⟩ := triple_of_callW
    (proofIrrelHalf_spec p hp.proofIrrelHalf n' ⟨s₀.mem, Locals.init []⟩ mode vis d a) c1
  rw [ht1] at hpa
  obtain ⟨a1, hA1, hCA1, hw1⟩ := pihW_ok p hp hld n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega)
    dn vis fe eb mode d a hm4 hebm ha s₀.mem a₀ MM hS (ra.headD 0) m1 hpa
  by_cases hwa : ra.headD 0 = 0
  · rw [ite_eq_left hwa] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    rw [hwa] at hA1
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine CoreRef.of_run (proofIrrel_run_none (coreKnot (decMode mode) fe id F) fe d.toNat (decE a)
      (decE b) a₀ a1 hA1) hCA1 ?_ ?_
    · show false = (r.headD 0 != 0); rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [ite_eq_right hwa] at hW
  rcases c2 : callW p (n' + 1) "proof_irrel_half" [mode, vis, d, b] m1 with _ | ⟨rb, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨M1, hS1, hK1, hSt1⟩ := hCA1
  obtain ⟨t2, ht2, -, hpb⟩ := triple_of_callW
    (proofIrrelHalf_spec p hp.proofIrrelHalf n' ⟨m1, Locals.init []⟩ mode vis d b) c2
  rw [ht2] at hpb
  obtain ⟨a2, hA2, hCA2, hw2⟩ := pihW_ok p hp hld n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega)
    dn vis fe eb mode d b hm4 hebm hb m1 a1 M1 hS1 (rb.headD 0) m2 hpb
  have hCA := CoreAfter.comp hK1 hSt1 hCA2
  have hrunF := proofIrrel_run_half (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
    a₀ a1 a2 (ra.headD 0) (rb.headD 0) hwa hA1 hA2
  by_cases hwb : rb.headD 0 = 0
  · rw [ite_eq_left hwb] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine CoreRef.of_run hrunF hCA ?_ ?_
    · show _ = (r.headD 0 != 0); rw [hr0, hwb]; simp
    · unfold ResH HW; rw [hr0]; decide
  · rw [ite_eq_right hwb] at hW
    obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
    have hr0 : r.headD 0 = (if ra.headD 0 = 1 then 0 else 1) &&& (if rb.headD 0 = 1 then 0 else 1) := by
      simpa using hr.symm
    refine CoreRef.of_run hrunF hCA ?_ ?_
    · show _ = (r.headD 0 != 0); rw [hr0]
      generalize ra.headD 0 = va at *
      generalize rb.headD 0 = vb at *
      by_cases h1 : va = 1 <;> by_cases h2 : vb = 1 <;> simp [h1, h2, hwb]
    · unfold ResH HW; rw [hr0]
      generalize ra.headD 0 = va
      generalize rb.headD 0 = vb
      by_cases h1 : va = 1 <;> by_cases h2 : vb = 1 <;> simp [h1, h2] <;> decide

/-- **`proof_irrel` refines `proofIrrel`.** Statement changes (the knot's slots, `lvl_eq_c` and the
level readback need them): `n ≤ 2 ^ 62`, the eager bit `eb = (mode >>> 1) &&& 1`; the
`CoreS.lvl_den` stub; the L code calls the cached `lvl_eq_c` (not `lvl_eq`) and is split in two
halves (`proof_irrel_half`, fuel). -/
@[refines ConRon.Arena.proofIrrel]
theorem proofIrrel_refines (p : Prog) (hp : IotaProg4 p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb :=
  proofIrrel_refines' p hp (fun _ _ _ _ _ _ _ hS => hS.lvl_den)

/-! ## `prepare_major(mode, vis, d, rec, ro, rc, major)` -/

/-- The tail of `prepare_major`'s non-K arm, from the rescued major `me`. -/
def pmTail (p : Prog) (n : Nat) (mode vis d rec ro rc me : Word) (m3 : Mem) :
    Option (Word × Mem) :=
  match callW p n "is_ctor_app" [vis, me] m3 with
  | none => none
  | some (r4, m4) =>
  if r4.headD 0 ≠ 0 then some (me, m4) else
  match callW p n "whnf" [mode, vis, d, me] m4 with
  | none => none
  | some (r5, m5) =>
  match callW p n "lit_major_to_ctor" [mode, vis, d, r5.headD 0] m5 with
  | none => none
  | some (r6, m6) =>
  match callW p n "major_to_ctor" [mode, vis, d, rec, ro, rc, r6.headD 0] m6 with
  | none => none
  | some (r7, m7) => some (r7.headD 0, m7)

/-- Model of `prepare_major`. -/
def pmW (p : Prog) (n : Nat) (m : Mem) (mode vis d rec ro rc major : Word) :
    Option (Word × Mem) :=
  match callW p n "rec_rule_k" [ro, rc] m with
  | none => none
  | some (rk, m1) =>
  if rk.headD 0 ≠ 0 then
    match callW p n "major_to_ctor" [mode, vis, d, rec, ro, rc, major] m1 with
    | none => none
    | some (r2, m2) =>
    match callW p n "is_ctor_app" [vis, r2.headD 0] m2 with
    | none => none
    | some (r3, m3) =>
    if r3.headD 0 ≠ 0 then
      match callW p n "lit_major_to_ctor" [mode, vis, d, r2.headD 0] m3 with
      | none => none
      | some (r4, m4) => some (r4.headD 0, m4)
    else some (r2.headD 0, m3)
  else
    match callW p n "is_str_lit" [major] m1 with
    | none => none
    | some (r2, m2) =>
    if r2.headD 0 ≠ 0 then pmTail p n mode vis d rec ro rc major m2 else
    match callW p n "major_to_ctor" [mode, vis, d, rec, ro, rc, major] m2 with
    | none => none
    | some (r, m') => pmTail p n mode vis d rec ro rc (r.headD 0) m'

theorem prepareMajor_spec (p : Prog) (hp : p.lookup "prepare_major" = some prepareMajorL) (n : Nat)
    (s₀ : St) (mode vis d rec ro rc major : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "prepare_major" [mode, vis, d, rec, ro, rc, major]
    ⦃fun r s' => LocEq s' s₀ ∧ pmW p n s₀.mem mode vis d rec ro rc major = some (r.headD 0, s'.mem);
      ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, prepareMajorL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
    callW_spec p n "rec_rule_k", callW_spec p n "major_to_ctor", callW_spec p n "is_ctor_app",
    callW_spec p n "lit_major_to_ctor", callW_spec p n "is_str_lit", callW_spec p n "whnf"] <;>
  simp_all [pmW, pmTail, Cmp.eval, LocEq, St.setLocs_cons,
    St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]


section pmRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (rec : NIdx)
  (rules : List IRecRule) (major : EIdx)

theorem prepareMajor_run_K_not (hK : recRuleK rules = true) (a a1 a2 : AState) (mk : EIdx)
    (h1 : (majorToCtor mode r fe d rec rules major).run a = .ok (mk, a1))
    (h2 : (isCtorApp fe mk).run a1 = .ok (false, a2)) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (mk, a2) := by
  simp only [prepareMajor, hK, ↓reduceIte, StateT.run_bind, h1, h2, except_ok_bind]
  simp; rfl

theorem prepareMajor_run_K_ctor (hK : recRuleK rules = true) (a a1 a2 a3 : AState) (mk res : EIdx)
    (h1 : (majorToCtor mode r fe d rec rules major).run a = .ok (mk, a1))
    (h2 : (isCtorApp fe mk).run a1 = .ok (true, a2))
    (h3 : (litMajorToCtor r fe d mk).run a2 = .ok (res, a3)) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (res, a3) := by
  simp only [prepareMajor, hK, ↓reduceIte, StateT.run_bind, h1, h2, h3, except_ok_bind]

/-- The non-K arm, a `String`-literal major (no rescue attempt first), a constructor application. -/
theorem prepareMajor_run_nk_str_ctor (hK : recRuleK rules = false) (a a1 a2 : AState)
    (hs : (isStrLit major).run a = .ok (true, a1))
    (hc : (isCtorApp fe major).run a1 = .ok (true, a2)) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (major, a2) := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind]
  simp only [StateT.run_pure, pure_bind, except_ok_bind, hc]
  simp; rfl

theorem prepareMajor_run_nk_str_fire (hK : recRuleK rules = false) (a a1 a2 a3 a4 a5 : AState)
    (m0 m1 res : EIdx)
    (hs : (isStrLit major).run a = .ok (true, a1))
    (hc : (isCtorApp fe major).run a1 = .ok (false, a2))
    (hw : (r.whnf d major).run a2 = .ok (m0, a3))
    (hl : (litMajorToCtor r fe d m0).run a3 = .ok (m1, a4))
    (hf : (majorToCtor mode r fe d rec rules m1).run a4 = .ok (res, a5)) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (res, a5) := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind, pure_bind, hc, hw, hl, hf]

theorem prepareMajor_run_nk_not_ctor (hK : recRuleK rules = false) (a a1 a2 a3 : AState)
    (me : EIdx)
    (hs : (isStrLit major).run a = .ok (false, a1))
    (hE : (majorToCtor mode r fe d rec rules major).run a1 = .ok (me, a2))
    (hc : (isCtorApp fe me).run a2 = .ok (true, a3)) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (me, a3) := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind,
    hE, hc]
  simp; rfl

theorem prepareMajor_run_nk_not_fire (hK : recRuleK rules = false) (a a1 a2 a3 a4 a5 a6 : AState)
    (me m0 m1 res : EIdx)
    (hs : (isStrLit major).run a = .ok (false, a1))
    (hE : (majorToCtor mode r fe d rec rules major).run a1 = .ok (me, a2))
    (hc : (isCtorApp fe me).run a2 = .ok (false, a3))
    (hw : (r.whnf d me).run a3 = .ok (m0, a4))
    (hl : (litMajorToCtor r fe d m0).run a4 = .ok (m1, a5))
    (hf : (majorToCtor mode r fe d rec rules m1).run a5 = .ok (res, a6)) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (res, a6) := by
  simp only [prepareMajor, hK, Bool.false_eq_true, ↓reduceIte, StateT.run_bind, hs, except_ok_bind,
    hE, hc, hw, hl, hf]

end pmRun


/-- The twin side of `pmTail`: the rescued major `me` is a constructor application (`res = me`), or
it is head-normalized, its literal converted, and the rescue tried again. -/
def PmTail (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (rec : NIdx)
    (rules : List IRecRule) (me : EIdx) (a : AState) (res : EIdx) (a' : AState) : Prop :=
  ((isCtorApp fe me).run a = .ok (true, a') ∧ res = me) ∨
  ∃ (a3 a4 a5 : AState) (m0 m1 : EIdx), (isCtorApp fe me).run a = .ok (false, a3) ∧
    (r.whnf d me).run a3 = .ok (m0, a4) ∧ (litMajorToCtor r fe d m0).run a4 = .ok (m1, a5) ∧
    (majorToCtor mode r fe d rec rules m1).run a5 = .ok (res, a')

theorem prepareMajor_run_nk_str (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (rec : NIdx) (rules : List IRecRule) (major : EIdx) (hK : recRuleK rules = false)
    (a a1 a2 : AState) (res : EIdx) (hs : (isStrLit major).run a = .ok (true, a1))
    (ht : PmTail mode r fe d rec rules major a1 res a2) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (res, a2) := by
  rcases ht with ⟨hc, hres⟩ | ⟨a3, a4, a5, m0, m1, hc, hw, hl, hf⟩
  · rw [hres]; exact prepareMajor_run_nk_str_ctor mode r fe d rec rules major hK a a1 a2 hs hc
  · exact prepareMajor_run_nk_str_fire mode r fe d rec rules major hK a a1 a3 a4 a5 a2 m0 m1 res
      hs hc hw hl hf

theorem prepareMajor_run_nk_not (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (rec : NIdx) (rules : List IRecRule) (major : EIdx) (hK : recRuleK rules = false)
    (a a1 a2 a3 : AState) (me res : EIdx) (hs : (isStrLit major).run a = .ok (false, a1))
    (hE : (majorToCtor mode r fe d rec rules major).run a1 = .ok (me, a2))
    (ht : PmTail mode r fe d rec rules me a2 res a3) :
    (prepareMajor mode r fe d rec rules major).run a = .ok (res, a3) := by
  rcases ht with ⟨hc, hres⟩ | ⟨a3', a4, a5, m0, m1, hc, hw, hl, hf⟩
  · rw [hres]; exact prepareMajor_run_nk_not_ctor mode r fe d rec rules major hK a a1 a2 a3 me hs hE hc
  · exact prepareMajor_run_nk_not_fire mode r fe d rec rules major hK a a1 a2 a3' a4 a5 a3 me m0 m1
      res hs hE hc hw hl hf

/-- **The knot's functions leave the record pool alone** (new stub assumption, as `ErecKept`: the
environment's record pool grows only when a declaration is installed, never during a term check). -/
def ErecKeptKnot (p : Prog) : Prop :=
  ∀ (n : Nat) (f : FnName) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
    f ∈ ["whnf", "infer_io", "lit_major_to_ctor", "is_ctor_app", "is_str_lit", "major_to_ctor",
      "prepare_major", "proof_irrel", "defeq_list", "iota_index_ok"] →
    callW p n f vs m = some (r, m') → m'.arr64 EREC = m.arr64 EREC

set_option maxRecDepth 8192 in
/-- `ErecKeptKnot` from the core's write set (`CoreErec.lean`). -/
theorem ErecKeptKnot.of_closed {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) :
    ErecKeptKnot p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closed hcl (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h

/-- **The tail of `prepare_major`'s non-K arm.** -/
theorem pmTail_ok (p : Prog) (hp : IotaProg4 p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hE : ErecKeptKnot p) (N : Nat) (hk : KnotUpTo p (N + 1)) (F : Nat) (hnF : N + 1 ≤ F) (hn62 : N + 1 ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (eb mode d rec ro rc me : Word)
    (rules : List IRecRule) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hme : HW me)
    (m3 : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m3 a vis fe M eb)
    (hrules : decRules (m3.arr64 EREC) ro.toNat rc.toNat = some rules)
    (w : Word) (mF : Mem) (h : pmTail p (N + 1) mode vis d rec ro rc me m3 = some (w, mF)) :
    ∃ a', PmTail (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE me) a (decE w) a' ∧ CoreAfter dn m3 mF a' vis fe M eb ∧ HW w := by
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  simp only [pmTail] at h
  rcases c4 : callW p (N + 1) "is_ctor_app" [vis, me] m3 with _ | ⟨r4, m4⟩ <;>
    simp only [c4, reduceCtorEq] at h
  obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, hr4⟩ := CoreSpec.run
    (isCtorApp_refines p hp.toIotaProg' N ⟨m3, Locals.init []⟩ a dn vis fe M eb me hS hme) c4
  by_cases hc4 : r4.headD 0 ≠ 0
  · rw [ite_eq_left hc4] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rw [decBool_t_m2c hc4] at hrun4
    exact ⟨_, Or.inl ⟨hrun4, rfl⟩, ⟨M4, hS4, hK4, hSt4⟩, hme⟩
  rw [ite_eq_right hc4] at h
  have hb : decBool r4 = false := by
    unfold decBool; have : r4.headD 0 = 0 := Classical.not_not.mp hc4
    rw [this]; rfl
  rw [hb] at hrun4
  rcases c5 : callW p (N + 1) "whnf" [mode, vis, d, me] m4 with _ | ⟨r5, m5⟩ <;>
    simp only [c5, reduceCtorEq] at h
  obtain ⟨hrun5, ⟨M5, hS5, hK5, hSt5⟩, hr5⟩ := CoreSpec.run
    ((hk (N + 1) (Nat.le_refl _)).whnf F ⟨m4, Locals.init []⟩ _ dn vis fe M4 eb mode d me hnF hn62
      ⟨hS4, hm4, hebm⟩ hme) c5
  rcases c6 : callW p (N + 1) "lit_major_to_ctor" [mode, vis, d, r5.headD 0] m5 with _ | ⟨r6, m6⟩ <;>
    simp only [c6, reduceCtorEq] at h
  obtain ⟨hrun6, ⟨M6, hS6, hK6, hSt6⟩, hr6⟩ := CoreSpec.run
    (litMajorToCtor_refines' p hp.toIotaProg' hc hw hsup N hk' F (by omega) (by omega)
      ⟨m5, Locals.init []⟩ _ dn vis fe M5 eb mode d (r5.headD 0) hS5 hm4 hebm hr5) c6
  rcases c7 : callW p (N + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, r6.headD 0] m6 with _ | ⟨r7, m7⟩ <;>
    simp only [c7, reduceCtorEq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have e4 : m4.arr64 EREC = m3.arr64 EREC := hE _ _ _ _ _ _ (by simp) c4
  have e5 : m5.arr64 EREC = m4.arr64 EREC := hE _ _ _ _ _ _ (by simp) c5
  have e6 : m6.arr64 EREC = m5.arr64 EREC := hE _ _ _ _ _ _ (by simp) c6
  have hrules6 : decRules (m6.arr64 EREC) ro.toNat rc.toNat = some rules := by
    rw [e6, e5, e4]; exact hrules
  obtain ⟨hrun7, ⟨M7, hS7, hK7, hSt7⟩, hr7⟩ := CoreSpec.run
    (hmtc N hk' F (by omega) ⟨m6, Locals.init []⟩ _ dn vis fe M6 eb mode d rec ro rc (r6.headD 0)
      rules (by omega) hS6 hm4 hebm hr6 hrules6) c7
  exact ⟨_, Or.inr ⟨_, _, _, _, _, hrun4, hrun5, hrun6, hrun7⟩,
    ⟨M7, hS7, hK4.trans (hK5.trans (hK6.trans hK7)), hSt4.trans (hSt5.trans (hSt6.trans hSt7))⟩, hr7⟩

/-- **`prepare_major` refines `prepareMajor`.** Statement changes: `n ≤ 2 ^ 62`, the eager bit
`eb = (mode >>> 1) &&& 1`, and the callees' hypotheses (`MajorToCtorOK`, `SupKeep`). -/
theorem prepareMajor_refines' (p : Prog) (hp : IotaProg4 p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hE : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (s₀.mem.arr64 EREC) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "prepare_major" [mode, vis, d, rec, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI rec) rules
        (decE major)) decH s₀ a₀ dn vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec ro rc major rules hS hm4 hebm hmaj hr
  refine triple_post (prepareMajor_spec p hp.prepareMajor n s₀ mode vis d rec ro rc major) fun r s'
    ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  simp only [pmW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  rcases c1 : callW p (N + 1) "rec_rule_k" [ro, rc] s₀.mem with _ | ⟨rk, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨t1, ht1, hmem1, -, hkk⟩ := triple_of_callW
    (recRuleK_refines p hp.recRuleK (N + 1) ⟨s₀.mem, Locals.init []⟩ ro rc rules
      (by have := hS.erec; show (s₀.mem.arr64 EREC).size < 2 ^ 64; omega) hr) c1
  have hm1 : m1 = s₀.mem := by rw [← ht1]; exact hmem1
  subst hm1
  have hk' : KnotUpTo p N := hk.mono (Nat.le_succ N)
  by_cases hkr : rk.headD 0 ≠ 0
  · -- the K arm
    rw [ite_eq_left hkr] at hW
    have hK : recRuleK rules = true := by rw [← hkk]; simpa using hkr
    rcases c2 : callW p (N + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major] s₀.mem with _ | ⟨r2, m2⟩ <;>
      simp only [c2, reduceCtorEq] at hW
    obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
      (hmtc N hk' F (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d rec ro rc major rules
        (by omega) hS hm4 hebm hmaj hr) c2
    rcases c3 : callW p (N + 1) "is_ctor_app" [vis, r2.headD 0] m2 with _ | ⟨r3, m3⟩ <;>
      simp only [c3, reduceCtorEq] at hW
    obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, hr3⟩ := CoreSpec.run
      (isCtorApp_refines p hp.toIotaProg' N ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb (r2.headD 0) hS2 hr2) c3
    by_cases hc3 : r3.headD 0 ≠ 0
    · rw [ite_eq_left hc3] at hW
      rcases c4 : callW p (N + 1) "lit_major_to_ctor" [mode, vis, d, r2.headD 0] m3 with _ | ⟨r4, m4⟩ <;>
        simp only [c4, reduceCtorEq] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, hr4⟩ := CoreSpec.run
        (litMajorToCtor_refines' p hp.toIotaProg' hc hw hsup N hk' F (by omega) (by omega)
          ⟨m3, Locals.init []⟩ _ dn vis fe M3 eb mode d (r2.headD 0) hS3 hm4 hebm hr2) c4
      rw [decBool_t_m2c hc3] at hrun3
      exact CoreRef.of_run (prepareMajor_run_K_ctor (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI rec) rules (decE major) hK a₀ _ _ _ _ _ hrun2 hrun3 hrun4)
        ⟨M4, hS4, hK2.trans (hK3.trans hK4), hSt2.trans (hSt3.trans hSt4)⟩ (decH_of _ _ hr)
        (resH_of_m2c _ _ hr hr4)
    · rw [ite_eq_right hc3] at hW
      obtain ⟨hr, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
      rw [decBool_f_m2c (Classical.not_not.mp hc3)] at hrun3
      exact CoreRef.of_run (prepareMajor_run_K_not (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI rec) rules (decE major) hK a₀ _ _ _ hrun2 hrun3)
        ⟨M3, hS3, hK2.trans hK3, hSt2.trans hSt3⟩ (decH_of _ _ hr) (resH_of_m2c _ _ hr hr2)
  · rw [ite_eq_right hkr] at hW
    have hK0 : recRuleK rules = false := by rw [← hkk, Classical.not_not.mp hkr]; rfl
    rcases c2 : callW p (N + 1) "is_str_lit" [major] s₀.mem with _ | ⟨r2, m2⟩ <;>
      simp only [c2, reduceCtorEq] at hW
    obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
      (isStrLit_refines p hp.isStrLit (N + 1) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb major hS hmaj) c2
    have hrules2 : decRules (m2.arr64 EREC) ro.toNat rc.toNat = some rules := by
      rw [hE _ _ _ _ _ _ (by simp) c2]; exact hr
    by_cases hs2 : r2.headD 0 ≠ 0
    · rw [ite_eq_left hs2, decBool_t_m2c hs2] at *
      obtain ⟨a', hT, ⟨M', hS', hK', hSt'⟩, hw'⟩ := pmTail_ok p hp hc hw hsup hmtc hE N hk F hnF hn62
        dn vis fe eb mode d rec ro rc major rules hm4 hebm hmaj m2 _ M2 hS2 hrules2 _ _ hW
      exact CoreRef.of_run (prepareMajor_run_nk_str (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI rec) rules (decE major) hK0 a₀ _ _ _ hrun2 hT)
        ⟨M', hS', hK2.trans hK', hSt2.trans hSt'⟩ rfl hw'
    · rw [ite_eq_right hs2, decBool_f_m2c (Classical.not_not.mp hs2)] at *
      rcases c3 : callW p (N + 1) "major_to_ctor" [mode, vis, d, rec, ro, rc, major] m2 with _ | ⟨r3, m3⟩ <;>
        simp only [c3, reduceCtorEq] at hW
      obtain ⟨hrun3, ⟨M3, hS3, hK3, hSt3⟩, hr3⟩ := CoreSpec.run
        (hmtc N hk' F (by omega) ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d rec ro rc major rules
          (by omega) hS2 hm4 hebm hmaj hrules2) c3
      have hrules3 : decRules (m3.arr64 EREC) ro.toNat rc.toNat = some rules := by
        rw [hE _ _ _ _ _ _ (by simp) c3]; exact hrules2
      obtain ⟨a', hT, ⟨M', hS', hK', hSt'⟩, hw'⟩ := pmTail_ok p hp hc hw hsup hmtc hE N hk F hnF hn62
        dn vis fe eb mode d rec ro rc (r3.headD 0) rules hm4 hebm hr3 m3 _ M3 hS3 hrules3 _ _ hW
      exact CoreRef.of_run (prepareMajor_run_nk_not (decMode mode) (coreKnot (decMode mode) fe id F) fe
        d.toNat (decI rec) rules (decE major) hK0 a₀ _ _ _ _ _ hrun2 hrun3 hT)
        ⟨M', hS', hK2.trans (hK3.trans hK'), hSt2.trans (hSt3.trans hSt')⟩ rfl hw'

end L.Arena
