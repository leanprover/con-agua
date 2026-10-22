import ConAgua.Arena.WhnfIotaRefine3
import ConAgua.Arena.CoreLevels

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 4 (`proof_irrel`, `prepare_major`, …)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem view_sort_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h 16) (hg : h >>> 28 = 2) :
    a.store.view (decE h) = some (.sort (decI (rdW (m.arr64 SOREC) (idxW h * 2 + tierW h)))) ∧
    (rdW (m.arr64 SOREC) (idxW h * 2 + tierW h)).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hu⟩ := node_of m a h sortSch SoRecRel sohash (·.sorts) _ hR.sort hv.2
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
  else if rdW (m3.arr64 CTL) (16 + tierW (r3.headD 0)) ≤ idxW (r3.headD 0) then none
  else
  match callW p n "pin_word" [53] m3 with
  | none => none
  | some (z, m4) =>
  match callW p n "lvl_eq_c"
      [rdW (m3.arr64 SOREC) (idxW (r3.headD 0) * 2 + tierW (r3.headD 0)), z.headD 0] m4 with
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
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
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

/-- **STUB (invariant `CoreS` should carry).** A `sort` node of the store has a level that reads
back (`denoteL` is defined at its handle), and so does the pinned zero level. `lvl_eq_c` (lane
`levels`/`CoreLevels.lean`'s `lvlEqC_refines`) needs this, the twin's `readLevelM` fails on a
dangling handle. It is not derivable from `CoreS` as it stands; the fix is a `CoreS` field
(`sorry` here instead, as the other stubs). -/
theorem CoreS.lvl_den {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState} {vis : Word}
    {fe : IFEnv} {M : ModeMaps} {eb : Word} (hS : CoreS dn m a vis fe M eb) :
    (∀ (e : EIdx) (u : LIdx), a.store.view e = some (.sort u) → ∃ l, denoteL a.store.ls u = some l) ∧
    (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l) := sorry

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
    simp only [StateT.run_bind, g1, g2, g3, except_ok_bind, this]
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

theorem pihW_ok (p : Prog) (hp : IotaProg4 p) (n F : Nat) (hknot : KnotUpTo p n) (hnF : n ≤ F)
    (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d x : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hx : HW x)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) (w : Word) (m' : Mem)
    (h : pihW p n m mode vis d x = some (w, m')) :
    ∃ a', PiHalfRun (coreKnot (decMode mode) fe id F) d.toNat (decE x) a w a' ∧
      CoreAfter dn m m' a' vis fe M eb ∧ HW w := by
  simp only [pihW] at h
  cases c1 : callW p n "infer_io" [mode, vis, d, x] m with
  | none => rw [c1] at h; cases h
  | some q =>
  obtain ⟨r1, m1⟩ := q
  rw [c1] at h
  simp only at h
  obtain ⟨ok1, ⟨M1, hS1, hK1, hSt1⟩, res1, hr1⟩ := CoreSpec.of_callW
    ((hknot n (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d x hnF hn62
      ⟨hS, hm4, hebm⟩ hx) c1
  cases c2 : callW p n "infer_io" [mode, vis, d, r1.headD 0] m1 with
  | none => rw [c2] at h; cases h
  | some q =>
  obtain ⟨r2, m2⟩ := q
  rw [c2] at h
  simp only at h
  obtain ⟨ok2, ⟨M2, hS2, hK2, hSt2⟩, res2, hr2⟩ := CoreSpec.of_callW
    ((hknot n (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _ hnF hn62
      ⟨hS1, hm4, hebm⟩ hr1) c2
  cases c3 : callW p n "whnf" [mode, vis, d, r2.headD 0] m2 with
  | none => rw [c3] at h; cases h
  | some q =>
  obtain ⟨r3, m3⟩ := q
  rw [c3] at h
  simp only at h
  obtain ⟨ok3, ⟨M3, hS3, hK3, hSt3⟩, res3, hr3⟩ := CoreSpec.of_callW
    ((hknot n (Nat.le_refl _)).whnf F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ hnF hn62
      ⟨hS2, hm4, hebm⟩ hr2) c3
  have hrun1 := AM.run_of_ok _ _ ok1
  have hrun2 := AM.run_of_ok _ _ ok2
  have hrun3 := AM.run_of_ok _ _ ok3
  rw [res1] at hrun1
  rw [res2] at hrun2
  rw [res3] at hrun3
  have hKA : KeptAll M M3 eb := hK1.trans (hK2.trans hK3)
  have hStA : StackKept m m3 := hSt1.trans (hSt2.trans hSt3)
  by_cases h2 : r3.headD 0 >>> 28 ≠ 2
  · rw [if_pos h2] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, ⟨_, _, _, _, _, _, hrun1, hrun2, hrun3, Or.inl ⟨rfl, ?_, rfl⟩⟩,
      ⟨M3, hS3, hKA, hStA⟩, by unfold HW; decide⟩
    exact fun ht => h2 ((decE_tag_eq _ hr3 2 (by decide)).mp ht)
  rw [if_neg h2] at h
  have h2' : r3.headD 0 >>> 28 = 2 := by simpa using h2
  by_cases hv1 : tierW (r3.headD 0) ≠ 0 ∧ rdW (m3.arr64 CTL) 1 = 0
  · rw [if_pos hv1] at h; cases h
  rw [if_neg hv1] at h
  by_cases hv2 : rdW (m3.arr64 CTL) (16 + tierW (r3.headD 0)) ≤ idxW (r3.headD 0)
  · rw [if_pos hv2] at h; cases h
  rw [if_neg hv2] at h
  obtain ⟨hvw, hn32⟩ := view_sort_f m3 (AM.st _ _) hS3.arena.1 (r3.headD 0) hr3
    ⟨hv1, UInt64.not_le.mp hv2⟩ h2'
  generalize rdW (m3.arr64 SOREC) (idxW (r3.headD 0) * 2 + tierW (r3.headD 0)) = uw at hvw hn32 h
  cases c4 : callW p n "pin_word" [53] m3 with
  | none => rw [c4] at h; cases h
  | some q =>
  obtain ⟨r4, m4⟩ := q
  rw [c4] at h
  simp only at h
  obtain ⟨t4, ht4, hloc4, hpw⟩ := triple_of_callW
    (pinWord_specM p hp.pinw n ⟨m3, Locals.init []⟩ 53) c4
  have hpw' : pinWordM m3 53 = some (r4, m4) := by simpa [ht4] using hpw
  simp only [pinWordM] at hpw'
  split at hpw' <;> try (cases hpw'; done)
  simp only [Option.some.injEq, Prod.mk.injEq] at hpw'
  obtain ⟨hr4, hm4e⟩ := hpw'
  subst hm4e
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
  cases c5 : callW p (n' + 2) "lvl_eq_c" [uw, r4.headD 0] m3 with
  | none => rw [c5] at h; cases h
  | some q =>
  obtain ⟨r5, m5⟩ := q
  rw [c5] at h
  simp only at h
  obtain ⟨hdn1, hdn2⟩ := hS3.lvl_den
  obtain ⟨lu, hdu⟩ := hdn1 _ _ hvw
  have hzl : a3.pins.zeroLevel = decI (r4.headD 0) := by rw [hP.zeroLevel, hr4']
  obtain ⟨lz, hdz⟩ := hdn2
  rw [hzl] at hdz
  have hz32 : HW (r4.headD 0) := by rw [hr4']; exact hP.lv_lt.2.1
  obtain ⟨ok5, ⟨M5, hS5, hK5, hSt5⟩, res5, hr5⟩ := CoreSpec.of_callW
    (lvlEqC_refines p hp.lvl n' ⟨m3, Locals.init []⟩ a3 dn vis fe M3 eb hS3 uw (r4.headD 0)
      hn32 hz32 lu lz hdu hdz) c5
  have hrunL := AM.run_of_ok _ _ ok5
  rw [res5] at hrunL
  by_cases hw0 : r5.headD 0 = 0
  · rw [if_pos hw0] at h; cases h
  rw [if_neg hw0] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
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
      vis fe MM eb := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d a b hS hm4 hebm ha hb
  apply L.M.triple_of_run
  intro s r s' hs0 hrun
  obtain ⟨hloc, hW⟩ := L.M.of_run (P := fun s => s = s₀) hs0 hrun
    (proofIrrel_spec p hp.proofIrrel n s₀ mode vis d a b)
  subst hs0
  refine ⟨hloc, ?_⟩
  simp only [pirrW] at hW
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ n' =>
  cases c1 : callW p (n' + 1) "proof_irrel_half" [mode, vis, d, a] s.mem with
  | none => rw [c1] at hW; cases hW
  | some q =>
  obtain ⟨ra, m1⟩ := q
  rw [c1] at hW
  simp only at hW
  obtain ⟨t1, ht1, -, hpa⟩ := triple_of_callW
    (proofIrrelHalf_spec p hp.proofIrrelHalf n' ⟨s.mem, Locals.init []⟩ mode vis d a) c1
  rw [ht1] at hpa
  obtain ⟨a1, hA1, hCA1, hw1⟩ := pihW_ok p hp n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega)
    dn vis fe eb mode d a hm4 hebm ha s.mem a₀ MM hS (ra.headD 0) m1 hpa
  by_cases hwa : ra.headD 0 = 0
  · rw [if_pos hwa] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    rw [hwa] at hA1
    have hrun := proofIrrel_run_none (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
      a₀ a1 hA1
    obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrun
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact hCA1
    · rw [hres]; show false = (r.headD 0 != 0); rw [hr0]; rfl
    · unfold ResH HW; rw [hr0]; decide
  rw [if_neg hwa] at hW
  cases c2 : callW p (n' + 1) "proof_irrel_half" [mode, vis, d, b] m1 with
  | none => rw [c2] at hW; cases hW
  | some q =>
  obtain ⟨rb, m2⟩ := q
  rw [c2] at hW
  simp only at hW
  obtain ⟨M1, hS1, hK1, hSt1⟩ := hCA1
  obtain ⟨t2, ht2, -, hpb⟩ := triple_of_callW
    (proofIrrelHalf_spec p hp.proofIrrelHalf n' ⟨m1, Locals.init []⟩ mode vis d b) c2
  rw [ht2] at hpb
  obtain ⟨a2, hA2, hCA2, hw2⟩ := pihW_ok p hp n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega)
    dn vis fe eb mode d b hm4 hebm hb m1 a1 M1 hS1 (rb.headD 0) m2 hpb
  have hCA := CoreAfter.comp hK1 hSt1 hCA2
  have hrunF := proofIrrel_run_half (coreKnot (decMode mode) fe id F) fe d.toNat (decE a) (decE b)
    a₀ a1 a2 (ra.headD 0) (rb.headD 0) hwa hA1 hA2
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ hrunF
  by_cases hwb : rb.headD 0 = 0
  · rw [if_pos hwb] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hr0 : r.headD 0 = 0 := by simpa using hr.symm
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact hCA
    · rw [hres]; show _ = (r.headD 0 != 0); rw [hr0, hwb]
      simp
    · unfold ResH HW; rw [hr0]; decide
  · rw [if_neg hwb] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨hr, hm⟩ := hW
    have hr0 : r.headD 0 = (if ra.headD 0 = 1 then 0 else 1) &&& (if rb.headD 0 = 1 then 0 else 1) := by
      simpa using hr.symm
    refine ⟨hok, ?_, ?_, ?_⟩
    · rw [hst, ← hm]; exact hCA
    · rw [hres]; show _ = (r.headD 0 != 0); rw [hr0]
      generalize ra.headD 0 = va at *
      generalize rb.headD 0 = vb at *
      by_cases h1 : va = 1 <;> by_cases h2 : vb = 1 <;> simp [h1, h2, hwb]
    · unfold ResH HW; rw [hr0]
      generalize ra.headD 0 = va
      generalize rb.headD 0 = vb
      by_cases h1 : va = 1 <;> by_cases h2 : vb = 1 <;> simp [h1, h2] <;> decide

end L.Arena
