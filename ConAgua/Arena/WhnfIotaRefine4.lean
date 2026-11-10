module

import ConAgua.Arena.WhnfIotaRefine3
public import ConAgua.Arena.WhnfIotaRefine2
public import ConAgua.Arena.CoreLevels
public import ConAgua.Arena.CoreDen
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import ConAgua.Arena.RefWalk
import Std.WP.Triple.SpecLemmas
public import ConAgua.Verdict.WhnfModels3E
import all ConAgua.Arena.CoreLevels
import all ConAgua.Arena.Pins
import all ConAgua.Arena.WhnfIota

@[expose] public section

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 4 (`proof_irrel`, `prepare_major`, …)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

theorem view_sort_f (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h SORT) (hg : tagW h = 2) :
    a.store.view (decE h) = some (.sort (decI (tfld m SORT (tierW h) (idxW h) 0))) ∧
    (tfld m SORT (tierW h) (idxW h) 0).toNat < 2 ^ 32 := by
  obtain ⟨k, hk, hu⟩ := node_of m a h sortCS SoRecRel (·.sorts) _ hR.sort hv.2
  simp only [SoRecRel] at hu
  rw [hu, decI_word]
  exact ⟨by rw [view_tier m a hR h hh hv.1, get_sort _ h hh hg, Tbl.node?, hk]; rfl, word_lt _⟩

/-! ## `proof_irrel(mode, vis, d, a, b)` -/

/-- **`proof_irrel_half`'s model, both outcomes**: the `infer_io` and `whnf` slots, `pin_word`,
`lvl_eq_c` through their runs (`callE`). -/
l_model pihE_spec (p : Prog) (hf : p.lookup "proof_irrel_half" = some proofIrrelHalfL)
  fns [hf ↦ pihE list] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

/-- **`proof_irrel`'s model, for both outcomes**: its halves through `proof_irrel_half`'s. -/
l_model pirrE_spec (p : Prog) (hf : p.lookup "proof_irrel" = some proofIrrelL)
    (hh : p.lookup "proof_irrel_half" = some proofIrrelHalfL)
  fns [hf ↦ pirrE list]
  specs [pihE_spec p hh n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified

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
  ⟨fun e u hv => hS.den.sort e u hv, ⟨_, hS.den.zero⟩⟩

/-- **What `proof_irrel` needs of the store** (`CoreS.lvl_den`'s statement, as a named
hypothesis): a `sort` node's level and the pinned zero level read back. -/
def LvlDen : Prop :=
  ∀ (dn : NIdx → Option ConLeche.Name) (m : Mem) (a : AState) (vis : Word) (fe : IFEnv)
    (M : ModeMaps) (eb : Word), CoreS dn m a vis fe M eb →
    (∀ (e : EIdx) (u : LIdx), a.store.view e = some (.sort u) → ∃ l, denoteL a.store.ls u = some l) ∧
    (∃ l, denoteL a.store.ls a.pins.zeroLevel = some l)

/-- `LvlDen` from `CoreDen` (`StoreDen.sort`, `StoreDen.zero`). -/
theorem LvlDen.of_den (h : CoreDen) : LvlDen :=
  fun dn m a vis fe M eb hS => ⟨(h dn m a vis fe M eb hS).sort, ⟨_, (h dn m a vis fe M eb hS).zero⟩⟩

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
          vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
            callW_spec p 0 "lq_find", callW_spec p 0 "lvl_eq_rec"] <;>
          simp_all [callW_zero]) hc
      exact hF

/-- One half of the twin's `proofIrrel`, in continuation style. -/
def piHalfT (r : CoreFnsA) (depth : Nat) (x : EIdx) (k : Bool → AM Bool) : AM Bool := do
  let ta ← r.inferIO depth x
  let hh ← r.whnf depth (← r.inferIO depth ta)
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort uT => do
      let z ← zeroLevel
      let ok ← liftFueled "level comparison" (← lvlEq? uT z)
      k ok
    | _ => pure false
  else pure false

theorem proofIrrel_eq_halves (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) :
    proofIrrel r fe depth a b =
      piHalfT r depth a (fun okA => piHalfT r depth b (fun okB => pure (okA && okB))) := by rfl

/-- **One half of the twin's `proofIrrel` as a computation** (the twin side of
`proof_irrel_half`): `none` the type's head is not a sort, else the level comparison's verdict. -/
def piHalfA (r : CoreFnsA) (depth : Nat) (x : EIdx) : AM (Option Bool) := do
  let ta ← r.inferIO depth x
  let hh ← r.whnf depth (← r.inferIO depth ta)
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort uT => do
      let z ← zeroLevel
      let ok ← liftFueled "level comparison" (← lvlEq? uT z)
      pure (some ok)
    | _ => pure none
  else pure none

theorem piHalfT_eq (r : CoreFnsA) (d : Nat) (x : EIdx) (k : Bool → AM Bool) :
    piHalfT r d x k =
      (piHalfA r d x >>= fun o => match o with | none => pure false | some ok => k ok) := by
  simp only [piHalfT, piHalfA, bind_assoc]
  congr 1; funext ta; congr 1; funext tta; congr 1; funext hh
  split
  · simp only [bind_assoc]; congr 1; funext v; split <;> simp [bind_assoc]
  · simp

theorem proofIrrel_run_none (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a b : EIdx) (s s' : AState)
    (h : (piHalfA r d a).run s = .ok (none, s')) :
    (proofIrrel r fe d a b).run s = .ok (false, s') := by
  rw [proofIrrel_eq_halves, piHalfT_eq, StateT.run_bind, h]; rfl

theorem proofIrrel_run_half (r : CoreFnsA) (fe : IFEnv) (d : Nat) (a b : EIdx) (s s1 s2 : AState)
    (x : Bool) (ob : Option Bool) (ha : (piHalfA r d a).run s = .ok (some x, s1))
    (hb : (piHalfA r d b).run s1 = .ok (ob, s2)) :
    (proofIrrel r fe d a b).run s = .ok ((ob.map (x && ·)).getD false, s2) := by
  rw [proofIrrel_eq_halves, piHalfT_eq, StateT.run_bind, ha]
  show (piHalfT r d b (fun okB => pure (x && okB))).run s1 = _
  rw [piHalfT_eq, StateT.run_bind]
  cases ob <;> (rw [hb]; rfl)

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
      vcgen [evalE_tagE, evalE_idxAE, evalE_idxGE, exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [pinWordM, pinW_eq, rdW_eq]

/-- **What `proof_irrel_half`'s errors claim from**: the knot's error half up to `n`, `pin_word`
and `lvl_eq_c` outside the verdict closure. -/
structure PihG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  pin : ∀ k args m e, callE p k "pin_word" args m = .error e → e.cls = 0
  lvl : ∀ k args m e, callE p k "lvl_eq_c" args m = .error e → e.cls = 0

/-- **`proof_irrel_half` refines `piHalfA`, both outcomes**: the slots by the knot, the sort's
level comparison by `lvl_eq_c` (out of fuel the twin's `liftFueled` fails). -/
theorem pih_ref (p : Prog) (hp : IotaProg4 p) (hld : LvlDen) (n F : Nat) (hknot : KnotUpTo p n)
    (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d x : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (hx : HW x)
    (m : Mem) (a : AState) (M : ModeMaps) (hS : CoreS dn m a vis fe M eb) :
    RefE (PihG p n) (pihE p (n + 1) m mode vis d x)
      (piHalfA (coreKnot (decMode mode) (decEager mode) fe id F) d.toNat (decE x)) a
      (fun v y a' => CorePost (fun r => decO (r.headD 0)) dn m vis fe M eb ResH v y a') := by
  simp only [pihE]
  unfold piHalfA
  have hK := hknot n (Nat.le_refl _)
  refine RefE.bind_callE (fun _ => rfl)
    (hK.inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb mode d x hnF hn62 ⟨hS, hm4, hebm⟩ hx)
    (fun (hG : PihG p n) => (hG.knot n (Nat.le_refl _)).inferIO F ⟨m, Locals.init []⟩ a dn vis fe M eb
      mode d x hnF hn62 ⟨hS, hm4, hebm⟩ hx) fun r1 m1 _ e1 => RefE.after_core (w := id) e1 fun M1 hS1 _ => ?_
  dsimp only [pihE.k_infer_io]
  refine RefE.bind_callE (fun _ => rfl)
    (hK.inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb mode d _ hnF hn62 ⟨hS1, hm4, hebm⟩ e1.resOk)
    (fun (hG : PihG p n) => (hG.knot n (Nat.le_refl _)).inferIO F ⟨m1, Locals.init []⟩ _ dn vis fe M1 eb
      mode d _ hnF hn62 ⟨hS1, hm4, hebm⟩ e1.resOk) fun r2 m2 _ e2 => RefE.after_core (w := id) e2 fun M2 hS2 _ => ?_
  dsimp only [pihE.k_infer_io_2]
  refine RefE.bind_callE (fun _ => rfl)
    (hK.whnf F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb mode d _ hnF hn62 ⟨hS2, hm4, hebm⟩ e2.resOk)
    (fun (hG : PihG p n) => (hG.knot n (Nat.le_refl _)).whnf F ⟨m2, Locals.init []⟩ _ dn vis fe M2 eb
      mode d _ hnF hn62 ⟨hS2, hm4, hebm⟩ e2.resOk) fun r3 m3 _ e3 => RefE.after_core (w := id) e3 fun M3 hS3 _ => ?_
  dsimp only [pihE.k_whnf]
  have hr3 : HW (r3.headD 0) := e3.resOk
  rw [show decH r3 = decE (r3.headD 0) from rfl]
  by_cases h2 : tagW (r3.headD 0) ≠ 2
  · rw [ite_eq_left h2]
    have htn : (decE (r3.headD 0)).tag ≠ ETag.sort :=
      fun ht => h2 ((decE_tag_eq _ hr3 2 (by decide)).mp ht)
    rw [beq_eq_false_iff_ne.mpr htn]
    exact RefE.ret rfl (CorePost.ret hS3 rfl (by unfold ResH HW; simp))
  rw [ite_eq_right h2]
  have h2' : tagW (r3.headD 0) = 2 := by simpa using h2
  refine RefE.abort0 (by rfl) fun hv1 => ?_
  refine RefE.abort0 (by rfl) fun hv2 => ?_
  generalize ha3 : AM.st _ _ = a3 at hS3
  obtain ⟨hvw, hn32⟩ := view_sort_f m3 a3 hS3.arena.base (r3.headD 0) hr3
    ⟨hv1, UInt64.not_le.mp hv2⟩ h2'
  have htag : (decE (r3.headD 0)).tag = ETag.sort := (decE_tag_eq _ hr3 2 (by decide)).mpr h2'
  rw [beq_iff_eq.mpr htag, ite_eq_left rfl]
  generalize tfld m3 SORT (tierW (r3.headD 0)) (idxW (r3.headD 0)) 0 = uw at hvw hn32 ⊢
  generalize decE (r3.headD 0) = hh at hvw ⊢
  have hv' : (view hh).run a3 = .ok (.sort (decI uw), a3) := by
    simp [view, hvw, StateT.run_bind, StateT.run_get]; rfl
  refine RefE.bind_right hv' ?_
  rcases c4 : callE p n "pin_word" [53] m3 with e4 | ⟨r4, m4⟩
  · simp only [pihE.k_pin_word]; exact fun hG => ErrClaim.of_cls0 (hG.pin _ _ _ _ c4)
  simp only [pihE.k_pin_word]
  obtain ⟨t4, ht4, -, hpw⟩ := triple_of_callE
    (pinWord_specM p hp.pinw n ⟨m3, Locals.init []⟩ 53) c4
  have hpw' : pinWordM m3 53 = some (r4, m4) := by simpa [ht4] using hpw
  obtain ⟨-, hpw'⟩ := of_ite_none hpw'
  obtain ⟨hr4, rfl⟩ := Prod.mk.inj (Option.some.inj hpw')
  have hP := hS3.pins
  have hr4' : r4.headD 0 = pinW m3 53 := by
    rw [← hr4]; simp [rdW, pinW]
  have hz : zeroLevel.run a3 = .ok (decI (r4.headD 0), a3) := by
    rw [hr4']; exact pinZeroLevel_run hP
  refine RefE.bind_right hz ?_
  rcases c5 : callE p n "lvl_eq_c" [uw, r4.headD 0] m3 with e5 | ⟨r5, m5⟩
  · simp only [pihE.k_lvl_eq_c]; exact fun hG => ErrClaim.of_cls0 (hG.lvl _ _ _ _ c5)
  simp only [pihE.k_lvl_eq_c]
  rcases Nat.lt_or_ge n 2 with hsm | hbig
  · have := lvlEqC_small p hp.lvl.c n hsm [uw, r4.headD 0] m3
    rw [callW_of_callE c5] at this; cases this
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 2 := ⟨n - 2, by omega⟩
  obtain ⟨hdn1, hdn2⟩ := hld _ _ _ _ _ _ _ hS3
  obtain ⟨lu, hdu⟩ := hdn1 _ _ hvw
  have hzl : a3.pins.zeroLevel = decI (r4.headD 0) := by rw [hP.zeroLevel, hr4']
  obtain ⟨lz, hdz⟩ := hdn2
  rw [hzl] at hdz
  have hz32 : HW (r4.headD 0) := by rw [hr4']; exact hP.lv_lt.2.1
  obtain ⟨hrunL, hA5, hr5⟩ := CoreSpec.run
    (lvlEqC_refines p hp.lvl n' ⟨m3, Locals.init []⟩ a3 dn vis fe M3 eb hS3 uw (r4.headD 0)
      hn32 hz32 lu lz hdu hdz) (callW_of_callE c5)
  refine RefE.bind_right hrunL ?_
  by_cases hw0 : r5.headD 0 = 0
  · rw [ite_eq_left hw0]
    have hdo : decO (r5.headD 0) = none := by rw [hw0]; rfl
    rw [hdo]
    exact RefE.bind_left fun _ => ErrClaim.fail _ _ rfl
  rw [ite_eq_right hw0]
  obtain ⟨y, hy⟩ : ∃ y, decO (r5.headD 0) = some y := by
    unfold decO; simp only [hw0, ↓reduceIte]; split <;> exact ⟨_, rfl⟩
  rw [hy]
  exact RefE.ret rfl ⟨hA5, (by show some y = decO (r5.headD 0); exact hy.symm), hr5⟩

theorem PihG.mono {p : Prog} {n n' : Nat} (h : PihG p n) (hn : n' ≤ n) : PihG p n' :=
  ⟨h.knot.mono hn, h.pin, h.lvl⟩

/-- **`proof_irrel` refines `proofIrrel`, both outcomes**: its halves' (`pih_ref`). -/
theorem pirr_ref (p : Prog) (hp : IotaProg4 p) (hld : LvlDen) (n F : Nat) (hk : KnotUpTo p n)
    (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d a b : Word) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1) (ha : HW a)
    (hb : HW b) (m : Mem) (a₀ : AState) (M : ModeMaps) (hS : CoreS dn m a₀ vis fe M eb) :
    RefE (PihG p n) (pirrE p (n + 1) m mode vis d a b)
      (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) a₀
      (CorePost decBool dn m vis fe M eb ResH) := by
  simp only [pirrE]
  rw [proofIrrel_eq_halves, piHalfT_eq]
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ n' =>
  refine RefE.bindE (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ n'))
    (pih_ref p hp hld n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega) dn vis fe eb mode d a hm4 hebm
      ha m a₀ M hS) fun ⟨ra, m1⟩ ya a1 _ hRa => ?_
  have hya : ya = decO (ra.headD 0) := hRa.res
  dsimp only [pirrE.k_proof_irrel_half]
  by_cases hwa : ra.headD 0 = 0
  · rw [ite_eq_left hwa, hya, hwa]
    exact RefE.ret rfl ⟨hRa.after, rfl, by show HW (0 : Word); unfold HW; decide⟩
  rw [ite_eq_right hwa]
  obtain ⟨M1, hS1, hK1, hSt1⟩ := hRa.after
  have hx : ya = some (decide (ra.headD 0 ≠ 1)) := by
    rw [hya]; unfold decO; by_cases h1 : ra.headD 0 = 1
    · rw [ite_eq_right hwa, ite_eq_left h1, h1]; rfl
    · rw [ite_eq_right hwa, ite_eq_right h1, decide_eq_true h1]
  rw [hx]
  simp only
  rw [piHalfT_eq]
  refine RefE.bindE (fun _ => rfl) (fun hG => hG.mono (Nat.le_succ n'))
    (pih_ref p hp hld n' F (hk.mono (Nat.le_succ n')) (by omega) (by omega) dn vis fe eb mode d b hm4 hebm
      hb m1 a1 M1 hS1) fun ⟨rb, m2⟩ yb a2 _ hRb => ?_
  have hyb : yb = decO (rb.headD 0) := hRb.res
  have hCA := CoreAfter.comp hK1 hSt1 hRb.after
  dsimp only [pirrE.k_proof_irrel_half_2]
  by_cases hwb : rb.headD 0 = 0
  · rw [ite_eq_left hwb, hyb, hwb]
    exact RefE.ret rfl ⟨hCA, rfl, by show HW (0 : Word); unfold HW; decide⟩
  rw [ite_eq_right hwb]
  refine RefE.ret (y := (yb.map (decide (ra.headD 0 ≠ 1) && ·)).getD false) ?_ ⟨hCA, ?_, ?_⟩
  · rw [hyb]; unfold decO; rw [ite_eq_right hwb]
    by_cases h2 : rb.headD 0 = 1
    · rw [ite_eq_left h2]; rfl
    · rw [ite_eq_right h2]; rfl
  · show _ = (_ != 0); rw [hyb]
    generalize ra.headD 0 = va at *
    generalize rb.headD 0 = vb at *
    by_cases h1 : va = 1 <;> by_cases h2 : vb = 1 <;> simp [decO, h1, h2, hwb]
  · show HW _
    unfold HW
    generalize ra.headD 0 = va
    generalize rb.headD 0 = vb
    by_cases h1 : va = 1 <;> by_cases h2 : vb = 1 <;> simp [h1, h2] <;> decide

/-- `proofIrrel_refines` over the named hypothesis `LvlDen` (`LvlDen.of_den` from `CoreDen`):
`pirr_ref`'s ok half. -/
theorem proofIrrel_refines' (p : Prog) (hp : IotaProg4 p) (hld : LvlDen) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d a b : Word), CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 →
    eb = (mode >>> 1) &&& 1 → HW a → HW b →
    CoreSpec p (n + 1) "proof_irrel" [mode, vis, d, a, b]
      (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d a b hS hm4 hebm ha hb =>
    RefE.coreSpec (pirrE_spec p hp.proofIrrel hp.proofIrrelHalf (n + 1) s₀ mode vis d a b)
      (pirr_ref p hp hld n F hk hnF hn62 dn vis fe eb mode d a b hm4 hebm ha hb s₀.mem a₀ MM hS)

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
      (proofIrrel (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE a) (decE b)) decBool s₀ a₀ dn
      vis fe MM eb :=
  proofIrrel_refines' p hp (fun _ _ _ _ _ _ _ hS => hS.lvl_den)

/-! ## `prepare_major(mode, vis, d, rec, ro, rc, major)` -/

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

/-- `major_to_ctor`'s error claim at fuel `N + 1` (the premises of `MajorToCtorOK`). -/
def MajorToCtorE (p : Prog) : Prop :=
  ∀ (N : Nat), KnotUpTo p N → KnotUpToE p N → ∀ (F : Nat), N ≤ F →
  ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec isK ro rc major : Word) (rules : List IRecRule),
    N ≤ 2 ^ 62 → CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 →
    HW major → decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules →
    CoreSpecE p (N + 1) "major_to_ctor" [mode, vis, d, rec, isK, ro, rc, major]
      (majorToCtor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules
        (decE major)) s₀ a₀

/-- **What `prepare_major`'s errors assume** at L fuel `n`: the knot's slots' claims, the verdict
closure (`lit_major_to_ctor`'s callees), `major_to_ctor`'s claim. -/
structure PmG (p : Prog) (n : Nat) : Prop where
  knot : KnotUpToE p n
  nv : closedNV p L.Checker.nvFns = true
  m2c : MajorToCtorE p

/-- The twin's `prepareMajor` past the rescued major `me` (non-K). -/
def pmTailT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (rec : NIdx)
    (rules : List IRecRule) (me : EIdx) : AM EIdx := do
  if ← isCtorApp fe me then pure me
  else do
    let major₀ ← r.whnf d me
    let major₁ ← litMajorToCtor r fe d major₀
    majorToCtor mode r fe d rec false rules major₁

theorem prepareMajor_nk (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (rec : NIdx) (rules : List IRecRule) (major : EIdx) :
    prepareMajor mode r fe d rec false rules major = (do
      let s ← isStrLit major
      let me ← if s then pure major else majorToCtor mode r fe d rec false rules major
      pmTailT mode r fe d rec rules me) := by
  simp only [prepareMajor, Bool.false_eq_true, ↓reduceIte, pmTailT]

/-- The record pool's decoded view across an ι callee. -/
theorem ErecKeptRec.erecP_eq {p : Prog} (hE : ErecKeptRec p) {n : Nat} {f : FnName} {vs : List Word}
    {m : Mem} {r : List Word} {m' : Mem} (hf : f ∈ iotaKeptFns := by simp [iotaKeptFns])
    (h : callW p n f vs m = some (r, m')) : erecP m' = erecP m :=
  (hE n f vs m r m' hf h).2.2.2

/-- The record pool (both tiers, the tagged reads, the decoded view) across an ι callee. -/
theorem ErecKeptRec.all {p : Prog} (hE : ErecKeptRec p) {n : Nat} {f : FnName} {vs : List Word}
    {m : Mem} {r : List Word} {m' : Mem} (hf : f ∈ iotaKeptFns)
    (h : callW p n f vs m = some (r, m')) :
    m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) ∧
      erRd m' = erRd m ∧ erecP m' = erecP m :=
  hE n f vs m r m' hf h

/-- Two such keeps in a row. -/
theorem erecKeep_trans {m m' m'' : Mem}
    (h2 : m''.arr64 EREC = m'.arr64 EREC ∧ m''.arr64 (tier1 EREC) = m'.arr64 (tier1 EREC) ∧
      erRd m'' = erRd m' ∧ erecP m'' = erecP m')
    (h1 : m'.arr64 EREC = m.arr64 EREC ∧ m'.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) ∧
      erRd m' = erRd m ∧ erecP m' = erecP m) :
    m''.arr64 EREC = m.arr64 EREC ∧ m''.arr64 (tier1 EREC) = m.arr64 (tier1 EREC) ∧
      erRd m'' = erRd m ∧ erecP m'' = erecP m :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.trans h1.2.2.2⟩

section pm
variable (p : Prog) (hp : IotaProg4 p) (hc : IotaCallees p) (hw : WhnfCallees p)
  (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p) (hE : ErecKeptRec p)
include hp hc hw hsup hmtc hE

omit hp hc hw hsup hmtc in
/-- **The tail of `prepare_major`'s non-K arm, both outcomes.** -/
theorem pmTail_ref (N : Nat) (hk : KnotUpTo p (N + 1)) (F : Nat) (hnF : N + 1 ≤ F)
    (hn62 : N + 1 ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d rec isK ro rc me : Word) (rules : List IRecRule) (hm4 : mode < 4) (hK : isK = 0)
    (hebm : eb = (mode >>> 1) &&& 1) (hme : HW me) (m3 : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m3 a vis fe M eb)
    (hrules : decRules (erecP m3) ro.toNat rc.toNat = some rules)
    (hp : IotaProg4 p) (hc : IotaCallees p) (hw : WhnfCallees p)
    (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p) :
    RefE (PmG p (N + 1)) (pmE.j1 p (N + 1) mode vis d rec isK ro rc me m3)
      (pmTailT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) rules (decE me))
      a (CorePost decH dn m3 vis fe M eb ResH) := by
  have hKf : (isK != 0) = false := by rw [hK]; rfl
  simp only [pmE.j1]
  unfold pmTailT
  refine RefE.bind_callW (fun _ => rfl) (isCtorApp_refines p hp.toIotaProg' N ⟨m3, Locals.init []⟩ a dn vis
    fe M eb me hS hme) fun r4 m4 c4 h4 => RefE.after_core (w := id) h4 fun M4 hS4 _ => ?_
  dsimp only [pmE.k_is_ctor_app_2]
  have e4 : erecP m4 = erecP m3 := hE.erecP_eq (by simp [iotaKeptFns]) c4
  by_cases hc4 : r4.headD 0 ≠ 0
  · rw [ite_eq_left hc4, decBool_t_m2c (by simpa using hc4)]
    exact RefE.ret rfl (CorePost.ret hS4 rfl hme)
  rw [ite_eq_right hc4, decBool_f_m2c (by simpa using hc4)]
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine RefE.bind_callE (fun _ => rfl) ((hk (N + 1) (Nat.le_refl _)).whnf F ⟨m4, Locals.init []⟩ _ dn vis fe
      M4 eb mode d me hnF hn62 ⟨hS4, hm4, hebm⟩ hme)
    (fun (hG : PmG p (N + 1)) => (hG.knot (N + 1) (Nat.le_refl _)).whnf F ⟨m4, Locals.init []⟩ _ dn vis fe M4
      eb mode d me hnF hn62 ⟨hS4, hm4, hebm⟩ hme) fun r5 m5 c5 h5 => RefE.after_core (w := id) h5 fun M5 hS5 _ => ?_
  dsimp only [pmE.k_whnf]
  have e5 : erecP m5 = erecP m4 := hE.erecP_eq (by simp [iotaKeptFns]) (callW_of_callE c5)
  refine RefE.bind_callE (s₀ := ⟨m5, Locals.init []⟩) (fun _ => rfl)
    (litMajorToCtor_refines' p hp.toIotaProg' hc hw hsup N (hk.mono (Nat.le_succ N)) F (by omega)
      (by omega) _ _ dn vis fe M5 eb mode d _ hS5 hm4 hebm h5.resOk)
    (fun hG => RefE.coreSpecE (lmtcE_spec p hp.litMajorToCtor (N + 1) _ mode vis d _) hG.nv
      (hG.knot.mono (Nat.le_succ N)) (lmtc_ref p hc hw hsup N (hk.mono (Nat.le_succ N)) F (by omega)
        (by omega) _ _ dn vis fe M5 eb mode d _ hS5 hm4 hebm h5.resOk))
    fun r6 m6 c6 h6 => RefE.after_core (w := id) h6 fun M6 hS6 _ => ?_
  have e6 : erecP m6 = erecP m5 := hE.erecP_eq (by simp [iotaKeptFns]) (callW_of_callE c6)
  dsimp only [pmE.k_lit_major_to_ctor_2]
  rw [← bind_pure (majorToCtor _ _ _ _ _ _ _ _), ← hKf]
  have hr6 : decRules (erecP m6) ro.toNat rc.toNat = some rules := by rw [e6, e5, e4]; exact hrules
  refine RefE.bind_callE (s₀ := ⟨m6, Locals.init []⟩) (fun _ => rfl)
    (hmtc N (hk.mono (Nat.le_succ N)) F (by omega) _ _ dn vis fe M6 eb mode d rec isK ro rc _ rules
      (by omega) hS6 hm4 hebm h6.resOk hr6)
    (fun hG => hG.m2c N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F (by omega) _ _
      dn vis fe M6 eb mode d rec isK ro rc _ rules (by omega) hS6 hm4 hebm h6.resOk hr6) (fun r7 m7 c7 h7 => ?_)
  obtain ⟨-, hP⟩ := h7.post
  exact RefE.ret rfl ⟨hP.after, rfl, hP.valid⟩

/-- **`prepare_major` refines `prepareMajor`, both outcomes**: the errors are `major_to_ctor`'s,
`lit_major_to_ctor`'s and the `whnf` slot's. -/
theorem pm_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec isK ro rc major : Word) (rules : List IRecRule)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hmaj : HW major) (hr : decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules) :
    RefE (PmG p n) (pmE p (n + 1) s₀.mem mode vis d rec isK ro rc major)
      (prepareMajor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules
        (decE major)) a₀ (CorePost decH dn s₀.mem vis fe MM eb ResH) := by
  cases n with
  | zero =>
    by_cases hkr : isK ≠ 0
    · obtain ⟨e, he, hc⟩ := callE_zero p "major_to_ctor" [mode, vis, d, rec, isK, ro, rc, major] s₀.mem
      rw [pmE.arm1 _ _ _ _ _ _ _ _ _ _ _ hkr, he, pmE.k_major_to_ctor.none]; exact RefE.of_cls0 hc
    · rw [pmE.arm2 _ _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hkr), callW_zero, liftE_none,
        pmE.k_is_str_lit.none]; exact RefE.of_cls0 (by simp)
  | succ N =>
  by_cases hkr : isK ≠ 0
  · -- the K arm
    rw [pmE.arm1 _ _ _ _ _ _ _ _ _ _ _ hkr]
    have hK : (isK != 0) = true := by simpa using hkr
    unfold prepareMajor
    rw [ite_eq_left hK]
    refine RefE.bind_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl)
      (hmtc N (hk.mono (Nat.le_succ N)) F (by omega) _ _ dn vis fe MM eb mode d rec isK ro rc major rules
        (by omega) hS hm4 hebm hmaj hr)
      (fun hG => hG.m2c N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F (by omega) _ _
        dn vis fe MM eb mode d rec isK ro rc major rules (by omega) hS hm4 hebm hmaj hr)
      fun r2 m2 _ h2 => RefE.after_core (w := id) h2 fun M2 hS2 _ => ?_
    dsimp only [pmE.k_major_to_ctor]
    refine RefE.bind_callW (fun _ => rfl) (isCtorApp_refines p hp.toIotaProg' N ⟨m2, Locals.init []⟩ _ dn vis
      fe M2 eb (r2.headD 0) hS2 h2.resOk) fun r3 m3 _ h3 => RefE.after_core (w := id) h3 fun M3 hS3 _ => ?_
    dsimp only [pmE.k_is_ctor_app]
    by_cases hc3 : r3.headD 0 ≠ 0
    · rw [ite_eq_left hc3, decBool_t_m2c (by simpa using hc3)]
      simp only [↓reduceIte]
      rw [← bind_pure (litMajorToCtor _ _ _ _)]
      refine RefE.bind_callE (s₀ := ⟨m3, Locals.init []⟩) (fun _ => rfl)
        (litMajorToCtor_refines' p hp.toIotaProg' hc hw hsup N (hk.mono (Nat.le_succ N)) F (by omega)
          (by omega) _ _ dn vis fe M3 eb mode d _ hS3 hm4 hebm h2.resOk)
        (fun hG => RefE.coreSpecE (lmtcE_spec p hp.litMajorToCtor (N + 1) _ mode vis d _) hG.nv
          (hG.knot.mono (Nat.le_succ N)) (lmtc_ref p hc hw hsup N (hk.mono (Nat.le_succ N)) F (by omega)
            (by omega) _ _ dn vis fe M3 eb mode d _ hS3 hm4 hebm h2.resOk)) (fun r4 m4 c4 h4 => ?_)
      obtain ⟨-, hP⟩ := h4.post
      exact RefE.ret rfl ⟨hP.after, rfl, hP.valid⟩
    · rw [ite_eq_right hc3, decBool_f_m2c (by simpa using hc3)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact RefE.ret rfl (CorePost.ret hS3 rfl h2.resOk)
  · -- the non-K arm
    have hK0 : isK = 0 := Classical.not_not.mp hkr
    rw [pmE.arm2 _ _ _ _ _ _ _ _ _ _ _ hK0]
    have hKf : (isK != 0) = false := by rw [hK0]; rfl
    rw [hKf, prepareMajor_nk]
    refine RefE.bind_callW (fun _ => rfl) (isStrLit_refines p hp.isStrLit (N + 1) s₀ a₀
      dn vis fe MM eb major hS hmaj) fun r2 m2 c2 h2 => RefE.after_core (w := id) h2 fun M2 hS2 _ => ?_
    dsimp only [pmE.k_is_str_lit]
    have hrules2 : decRules (erecP m2) ro.toNat rc.toNat = some rules := by
      rw [hE.erecP_eq (by simp [iotaKeptFns]) c2]; exact hr
    by_cases hs2 : r2.headD 0 ≠ 0
    · rw [ite_eq_left hs2, decBool_t_m2c (by simpa using hs2)]
      simp only [↓reduceIte, pure_bind]
      exact pmTail_ref p hE N hk F hnF hn62 dn vis fe eb mode d rec isK ro rc major
        rules hm4 hK0 hebm hmaj m2 _ M2 hS2 hrules2 hp hc hw hsup hmtc
    · rw [ite_eq_right hs2, decBool_f_m2c (by simpa using hs2)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hKf]
      refine RefE.bind_callE (s₀ := ⟨m2, Locals.init []⟩) (fun _ => rfl)
        (hmtc N (hk.mono (Nat.le_succ N)) F (by omega) _ _ dn vis fe M2 eb mode d rec isK ro rc major rules
          (by omega) hS2 hm4 hebm hmaj hrules2)
        (fun hG => hG.m2c N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F (by omega) _ _
          dn vis fe M2 eb mode d rec isK ro rc major rules (by omega) hS2 hm4 hebm hmaj hrules2)
        fun r3 m3 c3 h3 => RefE.after_core (w := id) h3 fun M3 hS3 _ => ?_
      have hrules3 : decRules (erecP m3) ro.toNat rc.toNat = some rules := by
        rw [hE.erecP_eq (by simp [iotaKeptFns]) (callW_of_callE c3)]; exact hrules2
      dsimp only [pmE.k_major_to_ctor_2]
      exact pmTail_ref p hE N hk F hnF hn62 dn vis fe eb mode d rec isK ro rc
        (r3.headD 0) rules hm4 hK0 hebm h3.resOk m3 _ M3 hS3 hrules3 hp hc hw hsup hmtc

/-- **`prepare_major` refines `prepareMajor`** (`pm_ref`'s ok half). -/
theorem prepareMajor_refines' :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec isK ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "prepare_major" [mode, vis, d, rec, isK, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules (decE major)) decH s₀ a₀ dn vis fe MM eb :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major rules hS hm4 hebm hmaj hr =>
    RefE.coreSpec (pmE_spec p hp.prepareMajor (n + 1) s₀ mode vis d rec isK ro rc major)
      (pm_ref p hp hc hw hsup hmtc hE n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major
        rules hS hm4 hebm hmaj hr)

end pm

end L.Arena
