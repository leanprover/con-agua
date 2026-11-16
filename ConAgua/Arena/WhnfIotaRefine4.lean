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
import ConAgua.Arena.IndView
import ConAgua.Arena.LdRd

@[expose] public section

/-!
# ι-reduction: proofs of `WhnfIota.lean`'s specs, part 4 (`proof_irrel`, `prepare_major`, …)
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

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

/-! ## `is_nat_succ_app(e)` -/

/-- **`is_nat_succ_app`'s model** (generated; `pin_word` through its model). -/
l_model isNatSuccApp_spec (p : Prog) (hp : IotaProg4 p)
  fns [hp.isNatSuccApp ↦ insaW]
  specs [pinWord_specM p hp.pinw n, callW_spec p n "pin_at"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rd_spec, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE]
  finish [tierW, idxW]

/-- **`is_nat_succ_app` refines `isNatSuccApp`** (read-only). -/
@[refines ConRon.Arena.isNatSuccApp]
theorem isNatSuccApp_refines (p : Prog) (hp : IotaProg4 p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb e : Word)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (he : HW e) :
    CoreSpec p (n + 1) "is_nat_succ_app" [e] (isNatSuccApp (decE e)) decBool s₀ a₀ dn vis fe MM eb := by
  refine triple_post (isNatSuccApp_spec p hp (n + 1) s₀ e) fun r s' ⟨hloc, hW⟩ => ⟨hloc, ?_⟩
  have hR := hS.arena.base
  have hres : ∀ (w : Word), (w = 0 ∨ w = 1) → some (w, s₀.mem) = some (r.headD 0, s'.mem) →
      (isNatSuccApp (decE e)).run a₀ = .ok (w != 0, a₀) →
      CoreRef (isNatSuccApp (decE e)) a₀ decBool dn s₀.mem vis fe MM eb r s'.mem ResH := by
    intro w hw h1 hrun
    obtain ⟨hr, hm⟩ := Prod.mk.inj (Option.some.inj h1)
    refine CoreRef.of_pure hS hrun hm.symm (by simp only [decBool]; rw [← hr]) ?_
    unfold ResH HW; rw [← hr]; rcases hw with rfl | rfl <;> decide
  simp only [insaW] at hW
  by_cases h4 : tagW e ≠ 4
  · simp only [h4, ne_eq, not_false_eq_true, ↓reduceIte] at hW
    refine hres 0 (.inl rfl) hW ?_
    simp only [isNatSuccApp, decE_tag_app_beq e he, h4, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  have h4' : tagW e = 4 := by simpa using h4
  simp only [h4, ↓reduceIte] at hW
  obtain ⟨hv1, hW⟩ := of_ite_none hW
  obtain ⟨hv2, hW⟩ := of_ite_none hW
  have hvo : viewOKA s₀.mem e := ⟨hv1, UInt64.not_le.mp hv2⟩
  obtain ⟨hva, hf, -⟩ := view_app s₀.mem a₀ hR e he hvo h4'
  have hpre : (isNatSuccApp (decE e)).run a₀ = (do
      let f := decE (tfld s₀.mem APP (tierW e) (idxA e) 0)
      if f.tag == ETag.const then
        match ← view f with
        | .const c us => do
          let el ← emptyLevels
          let ns ← pinNatSucc
          pure (us == el && c == ns)
        | _ => pure false
      else pure false : AM Bool).run a₀ := by
    simp only [isNatSuccApp, decE_tag_app_beq e he, h4', decide_true, ↓reduceIte, StateT.run_bind,
      view_run _ _ _ hva, except_ok_bind]
    rfl
  generalize tfld s₀.mem APP (tierW e) (idxA e) 0 = f at hf hW hpre
  by_cases f3 : tagW f ≠ 3
  · simp only [f3, ne_eq, not_false_eq_true, ↓reduceIte] at hW
    refine hres 0 (.inl rfl) hW ?_
    rw [hpre]; simp only [decE_tag_const_beq f hf, f3, decide_false, Bool.false_eq_true, ↓reduceIte]
    rfl
  have f3' : tagW f = 3 := by simpa using f3
  simp only [f3, ↓reduceIte] at hW
  obtain ⟨fv1, hW⟩ := of_ite_none hW
  obtain ⟨fv2, hW⟩ := of_ite_none hW
  have fvo : viewOK s₀.mem f CONST := ⟨fv1, UInt64.not_le.mp fv2⟩
  obtain ⟨hv, hn, hu⟩ := L.Ind.view_const_f s₀.mem a₀ hR f hf fvo f3'
  have hP := hS.pins
  have h0 : pinW s₀.mem 0 ≠ 0 := by
    intro h0; simp [pinWordM, h0, insaW.k_pin_word] at hW
  rw [show pinWordM s₀.mem 52 = some ([rdW (s₀.mem.arr64 PINS) 52], s₀.mem) by simp [pinWordM, h0]] at hW
  simp only [insaW.k_pin_word, List.headD_cons] at hW
  rcases c2 : callW p n "pin_at" [3] s₀.mem with _ | ⟨r2, m2⟩
  · rw [c2] at hW; simp [insaW.k_pin_at] at hW
  obtain ⟨s2, hs2, hm2, -, hr2, hpin⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (pinAt_refines p hp.pinat n ⟨s₀.mem, Locals.init []⟩ a₀ ⟨fun _ => hP⟩ 3) c2
  have hm2' : m2 = s₀.mem := hs2 ▸ hm2
  subst hm2'
  rw [c2] at hW
  simp only [insaW.k_pin_at] at hW
  have hpin3 := pinAt_run hP 3 (by decide)
  rw [show ((3 : Word).toNat) = 3 from rfl] at hpin
  rw [hpin3] at hpin
  have hns : r2.headD 0 = pinW s₀.mem (1 + 3) := by
    have := (Except.ok.inj hpin); exact (decI_inj_iff hr2 (hP.names_lt 3 (by decide))).mp (by
      have := congrArg Prod.fst this; exact this.symm)
  have hel := hP.lv_lt.1
  have hns' := hP.names_lt 3 (by decide)
  have hrun2 : (isNatSuccApp (decE e)).run a₀ = .ok (
      (decide (tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52) &&
        decide (tfld s₀.mem CONST (tierW f) (idxW f) 0 = pinW s₀.mem (1 + 3))), a₀) := by
    rw [hpre]
    simp only [decE_tag_const_beq f hf, f3', decide_true, ↓reduceIte, StateT.run_bind, view_run _ _ _ hv,
      except_ok_bind, emptyLevels, pinEmptyLevels_run hP, pinNatSucc, PIN_NAT_SUCC,
      pinAt_run hP 3 (by decide)]
    rw [decI_beq _ _ hu hel, decI_beq _ _ hn hns']
    rfl
  by_cases hc : tfld s₀.mem CONST (tierW f) (idxW f) 1 = rdW (s₀.mem.arr64 PINS) 52 ∧
      tfld s₀.mem CONST (tierW f) (idxW f) 0 = r2.headD 0
  · rw [ite_eq_left hc] at hW
    refine hres 1 (.inr rfl) hW ?_
    rw [hrun2, hns] at *
    rw [hrun2]
    have e1 : tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52 := by rw [hc.1]; rfl
    simp [e1, ← hns, hc.2]
  · rw [ite_eq_right hc] at hW
    refine hres 0 (.inl rfl) hW ?_
    rw [hrun2]
    have : ¬ (tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52 ∧
        tfld s₀.mem CONST (tierW f) (idxW f) 0 = pinW s₀.mem (1 + 3)) := by
      rw [← hns]; exact hc
    by_cases a1 : tfld s₀.mem CONST (tierW f) (idxW f) 1 = pinW s₀.mem 52
    · have a2 : ¬ tfld s₀.mem CONST (tierW f) (idxW f) 0 = pinW s₀.mem (1 + 3) := fun h => this ⟨a1, h⟩
      simp only [a1, a2, decide_true, decide_false, Bool.and_false]; rfl
    · simp only [a1, decide_false, Bool.false_and]; rfl

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
  obtain ⟨hvw, hn32⟩ := L.Ind.view_sort_f m3 a3 hS3.arena.base (r3.headD 0) hr3
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
    f ∈ ["whnf", "infer_io", "lit_major_to_ctor", "ctor_view", "is_str_lit", "is_nat_succ_app", "major_to_ctor", "major_to_ctor_rescue", "prepare_major", "prepare_major_whnf", "proof_irrel", "defeq_list", "iota_index_ok"] →
    callW p n f vs m = some (r, m') → m'.arr64 EREC = m.arr64 EREC

set_option maxRecDepth 8192 in
/-- `ErecKeptKnot` from the core's write set (`CoreErec.lean`). -/
theorem ErecKeptKnot.of_closed {p : Prog} (hcl : closedA p coreErecA coreErecC coreFns = true) :
    ErecKeptKnot p :=
  fun _ _ _ _ _ _ hf h => callW_erec_closed hcl (by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) h

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

/-- The twin's `prepareMajor` past the structure rescues' view `vE` (non-K). -/
def pmTailT (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (rec : NIdx)
    (rules : List IRecRule) (vE : MajorView) : AM MajorView := do
  if vE.isCtor then
    if ← isNatSuccApp vE.expr then prepareMajorWhnf mode r fe d rec false rules vE.expr
    else pure vE
  else prepareMajorWhnf mode r fe d rec false rules vE.expr

theorem prepareMajor_nk (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat)
    (rec : NIdx) (rules : List IRecRule) (major : EIdx) :
    prepareMajor mode r fe d rec false rules major = (do
      let s ← isStrLit major
      let vE ← if s then pure (.stuck major) else majorToCtor mode r fe d rec false rules major
      pmTailT mode r fe d rec rules vE) := by
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

/-- A five-word answer is its own five words. -/
theorem list5_eta (r : List Word) (h : r.length = 5) :
    [r.headD 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
      r.tail.tail.tail.tail.headD 0] = r := by
  match r, h with
  | [_, _, _, _, _], _ => rfl

/-- The view decodes alike over the same record pool. -/
theorem decMV_congr {m m' : Mem} (h : erecP m' = erecP m) (r : List Word) : decMV m' r = decMV m r := by
  unfold decMV; rw [h]

theorem MVOk_congr {m m' : Mem} (h : erecP m' = erecP m) {r : List Word} (hok : MVOk m' r) : MVOk m r := by
  unfold MVOk at *; rw [← h]; exact hok

theorem PmG.mono {p : Prog} {n n' : Nat} (h : PmG p n) (hn : n' ≤ n) : PmG p n' :=
  ⟨h.knot.mono hn, h.nv, h.m2c⟩

section pm
variable (p : Prog) (hp : IotaProg4 p) (hc : IotaCallees p) (hw : WhnfCallees p) (hmtc : MajorToCtorOK p) (hE : ErecKeptRec p)
include hp hc hw hmtc hE

omit hp hc hw hmtc hE in
theorem decMV_view_ctor {m : Mem} {t e c us q : Word} (hok : MVOk m [t, e, c, us, q]) (ht : t ≠ 0) :
    (decMV m [t, e, c, us, q]).isCtor = true := by
  obtain ⟨cv, nP, nF, ind, hq⟩ := hok.2.2.2.2 ht
  simp only [List.getD_cons_succ, List.getD_cons_zero] at hq
  rw [decMV_ctor ht hq]; rfl

omit hp hc hw hmtc hE in
theorem decMV_view_stuck (m : Mem) (e c us q : Word) : (decMV m [0, e, c, us, q]).isCtor = false := by
  rw [decMV_stuck]; rfl

omit hp hc hw hmtc hE in
theorem decMV_view_expr (m : Mem) (t e c us q : Word) : (decMV m [t, e, c, us, q]).expr = decE e :=
  decMV_expr m _

/-- **`prepare_major_whnf` refines `prepareMajorWhnf`, both outcomes**: the errors are the `whnf`
slot's, `lit_major_to_ctor`'s and `major_to_ctor`'s; the view's record read in `m₀` (the record
pool kept since). -/
theorem pmw_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d rec isK ro rc me : Word) (rules : List IRecRule) (hm4 : mode < 4)
    (hebm : eb = (mode >>> 1) &&& 1) (hme : HW me) (m₀ m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (he0 : erecP m = erecP m₀)
    (hrules : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (PmG p n) (pmwE p (n + 1) m mode vis d rec isK ro rc me)
      (prepareMajorWhnf (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules (decE me)) a (CorePost (decMV m₀) dn m vis fe M eb (MVOk m₀)) := by
  simp only [pmwE]
  cases n with
  | zero =>
    obtain ⟨e, he, hc0⟩ := callE_zero p "whnf" [mode, vis, d, me] m
    rw [he, pmwE.k_whnf.eq_1]; exact RefE.of_cls0 hc0
  | succ N =>
  unfold prepareMajorWhnf
  refine RefE.bind_callE (s₀ := ⟨m, Locals.init []⟩) (fun _ => rfl)
    ((hk (N + 1) (Nat.le_refl _)).whnf F ⟨m, Locals.init []⟩ _ dn vis fe M eb mode d me hnF hn62
      ⟨hS, hm4, hebm⟩ hme)
    (fun (hG : PmG p (N + 1)) => (hG.knot (N + 1) (Nat.le_refl _)).whnf F ⟨m, Locals.init []⟩ _ dn vis fe
      M eb mode d me hnF hn62 ⟨hS, hm4, hebm⟩ hme)
    fun r5 m5 c5 h5 => RefE.after_core (w := id) h5 fun M5 hS5 _ => ?_
  dsimp only [pmwE.k_whnf]
  have e5 : erecP m5 = erecP m := hE.erecP_eq (by simp [iotaKeptFns]) (callW_of_callE c5)
  refine RefE.bind_callE (s₀ := ⟨m5, Locals.init []⟩) (fun _ => rfl)
    (litMajorToCtor_refines' p hp.toIotaProg' hc hw N (hk.mono (Nat.le_succ N)) F (by omega)
      (by omega) _ _ dn vis fe M5 eb mode d _ hS5 hm4 hebm h5.resOk)
    (fun hG => RefE.coreSpecE (lmtcE_spec p hp.litMajorToCtor (N + 1) _ mode vis d _) hG.nv
      (hG.knot.mono (Nat.le_succ N)) (lmtc_ref p hc hw N (hk.mono (Nat.le_succ N)) F (by omega)
        (by omega) _ _ dn vis fe M5 eb mode d _ hS5 hm4 hebm h5.resOk))
    fun r6 m6 c6 h6 => RefE.after_core (w := id) h6 fun M6 hS6 _ => ?_
  have e6 : erecP m6 = erecP m5 := hE.erecP_eq (by simp [iotaKeptFns]) (callW_of_callE c6)
  dsimp only [pmwE.k_lit_major_to_ctor]
  rw [← bind_pure (majorToCtor _ _ _ _ _ _ _ _)]
  have hr6 : decRules (erecP m6) ro.toNat rc.toNat = some rules := by rw [e6, e5]; exact hrules
  refine RefE.bind_callE (s₀ := ⟨m6, Locals.init []⟩) (fun _ => rfl)
    (hmtc N (hk.mono (Nat.le_succ N)) F (by omega) _ _ dn vis fe M6 eb mode d rec isK ro rc _ rules
      (by omega) hS6 hm4 hebm h6.resOk hr6)
    (fun hG => hG.m2c N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F (by omega) _ _
      dn vis fe M6 eb mode d rec isK ro rc _ rules (by omega) hS6 hm4 hebm h6.resOk hr6)
    (fun r7 m7 c7 h7 => ?_)
  obtain ⟨-, hP⟩ := h7.post
  have e60 : erecP m6 = erecP m₀ := (e6.trans e5).trans he0
  have h5' := list5_eta r7 hP.valid.1
  dsimp only [pmwE.k_major_to_ctor]
  refine RefE.ret rfl ⟨hP.after, ?_, ?_⟩
  · rw [h5']; exact decMV_congr e60 r7
  · rw [h5']; exact MVOk_congr e60 hP.valid

/-- **`prepare_major_whnf`'s inlined model at the tail of `prepare_major`** (`pmE.j2`). -/
theorem pmJ2_ref (N : Nat) (hk : KnotUpTo p (N + 1)) (F : Nat) (hnF : N + 1 ≤ F)
    (hn62 : N + 1 ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d rec isK ro rc e : Word) (rules : List IRecRule) (hm4 : mode < 4) (hK : isK = 0)
    (hebm : eb = (mode >>> 1) &&& 1) (he : HW e) (m₀ m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (he0 : erecP m = erecP m₀)
    (hrules : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (PmG p (N + 1)) (pmE.j2 p (N + 1) mode vis d rec isK ro rc e m)
      (prepareMajorWhnf (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        false rules (decE e)) a (CorePost (decMV m₀) dn m vis fe M eb (MVOk m₀)) := by
  have hKf : (isK != 0) = false := by rw [hK]; rfl
  dsimp only [pmE.j2]
  rw [← bind_pure (prepareMajorWhnf _ _ _ _ _ _ _ _), ← hKf]
  refine RefE.bindE (fun _ => rfl) (fun (hG : PmG p (N + 1)) => hG.mono (Nat.le_succ N))
    (pmw_ref p hp hc hw hmtc hE N (hk.mono (Nat.le_succ N)) F (by omega) (by omega) dn vis fe eb mode d rec
      isK ro rc e rules hm4 hebm he m₀ m a M hS he0 hrules) fun v y a1 _ hQ => ?_
  dsimp only [pmE.k_major_to_ctor]
  have h5 := list5_eta v.1 hQ.valid.1
  exact RefE.ret rfl ⟨hQ.after, by rw [h5]; exact hQ.res, by rw [h5]; exact hQ.valid⟩

/-- **The view's tail of `prepare_major`** (`pmE.j1`, the non-K arm): a constructor view that is
`Nat.succ x` goes to `prepare_major_whnf`, as does a stuck one. -/
theorem pmJ1_ref (N : Nat) (hk : KnotUpTo p (N + 1)) (F : Nat) (hnF : N + 1 ≤ F)
    (hn62 : N + 1 ≤ 2 ^ 62) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (eb mode d rec isK ro rc t e c us q : Word) (rules : List IRecRule) (hm4 : mode < 4) (hK : isK = 0)
    (hebm : eb = (mode >>> 1) &&& 1) (he : HW e) (m₀ m : Mem) (a : AState) (M : ModeMaps)
    (hS : CoreS dn m a vis fe M eb) (he0 : erecP m = erecP m₀) (hok : MVOk m₀ [t, e, c, us, q])
    (hrules : decRules (erecP m) ro.toNat rc.toNat = some rules) :
    RefE (PmG p (N + 1)) (pmE.j1 p (N + 1) mode vis d rec isK ro rc t e c us q m)
      (pmTailT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec) rules
        (decMV m₀ [t, e, c, us, q])) a (CorePost (decMV m₀) dn m vis fe M eb (MVOk m₀)) := by
  dsimp only [pmE.j1]
  unfold pmTailT
  rw [decMV_view_expr]
  by_cases ht : t ≠ 0
  · rw [ite_eq_left ht, decMV_view_ctor hok ht]
    simp only [↓reduceIte]
    refine RefE.bind_callW (fun _ => rfl) (isNatSuccApp_refines p hp N ⟨m, Locals.init []⟩ a dn vis fe M eb
      e hS he) fun r4 m4 c4 h4 => RefE.after_core (w := id) h4 fun M4 hS4 _ => ?_
    dsimp only [pmE.k_is_nat_succ_app]
    have e4 : erecP m4 = erecP m := hE.erecP_eq (by simp [iotaKeptFns]) c4
    by_cases g : r4.headD 0 = 0
    · rw [ite_eq_left g, L.Arena.decBool_false_of g]
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact RefE.ret rfl (CorePost.ret hS4 rfl hok)
    · rw [ite_eq_right g, L.Arena.decBool_true_of g]
      simp only [↓reduceIte]
      exact pmJ2_ref p hp hc hw hmtc hE N hk F hnF hn62 dn vis fe eb mode d rec isK ro rc e rules hm4 hK hebm
        he m₀ m4 _ M4 hS4 (e4.trans he0) (by rw [e4]; exact hrules)
  · have ht0 : t = 0 := by simpa using ht
    rw [ite_eq_right ht]
    subst ht0
    rw [decMV_view_stuck]
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact pmJ2_ref p hp hc hw hmtc hE N hk F hnF hn62 dn vis fe eb mode d rec isK ro rc e rules hm4 hK hebm
      he m₀ m a M hS he0 hrules

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
        (decE major)) a₀ (CorePost (decMV s₀.mem) dn s₀.mem vis fe MM eb (MVOk s₀.mem)) := by
  cases n with
  | zero =>
    by_cases hkr : isK ≠ 0
    · obtain ⟨e, he, hc⟩ := callE_zero p "major_to_ctor" [mode, vis, d, rec, isK, ro, rc, major] s₀.mem
      rw [pmE.arm1 _ _ _ _ _ _ _ _ _ _ _ hkr, he, pmE.k_major_to_ctor.eq_1]; exact RefE.of_cls0 hc
    · rw [pmE.arm2 _ _ _ _ _ _ _ _ _ _ _ (Classical.not_not.mp hkr), callW_zero, liftE_none,
        pmE.k_is_str_lit.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  by_cases hkr : isK ≠ 0
  · rw [pmE.arm1 _ _ _ _ _ _ _ _ _ _ _ hkr]
    have hK : (isK != 0) = true := by simpa using hkr
    unfold prepareMajor
    rw [ite_eq_left hK, ← bind_pure (majorToCtor _ _ _ _ _ _ _ _)]
    refine RefE.bind_callE (s₀ := ⟨s₀.mem, Locals.init []⟩) (fun _ => rfl)
      (hmtc N (hk.mono (Nat.le_succ N)) F (by omega) _ _ dn vis fe MM eb mode d rec isK ro rc major rules
        (by omega) hS hm4 hebm hmaj hr)
      (fun hG => hG.m2c N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F (by omega) _ _
        dn vis fe MM eb mode d rec isK ro rc major rules (by omega) hS hm4 hebm hmaj hr)
      fun r2 m2 _ h2 => ?_
    obtain ⟨-, hP⟩ := h2.post
    dsimp only [pmE.k_major_to_ctor]
    have h5 := list5_eta r2 hP.valid.1
    exact RefE.ret rfl ⟨hP.after, by rw [h5], by rw [h5]; exact hP.valid⟩
  · have hK0 : isK = 0 := Classical.not_not.mp hkr
    rw [pmE.arm2 _ _ _ _ _ _ _ _ _ _ _ hK0]
    have hKf : (isK != 0) = false := by rw [hK0]; rfl
    rw [hKf, prepareMajor_nk]
    refine RefE.bind_callW (fun _ => rfl) (isStrLit_refines p hp.isStrLit (N + 1) s₀ a₀
      dn vis fe MM eb major hS hmaj) fun r2 m2 c2 h2 => RefE.after_core (w := id) h2 fun M2 hS2 _ => ?_
    dsimp only [pmE.k_is_str_lit]
    have e2 : erecP m2 = erecP s₀.mem := hE.erecP_eq (by simp [iotaKeptFns]) c2
    have hrules2 : decRules (erecP m2) ro.toNat rc.toNat = some rules := by rw [e2]; exact hr
    by_cases hs2 : r2.headD 0 ≠ 0
    · rw [ite_eq_left hs2, L.Arena.decBool_true_of (by simpa using hs2)]
      simp only [↓reduceIte, pure_bind]
      rw [show (MajorView.stuck (decE major)) = decMV s₀.mem [0, major, 0, 0, 0] from (decMV_stuck _ _ _ _ _).symm]
      exact pmJ1_ref p hp hc hw hmtc hE N hk F hnF hn62 dn vis fe eb mode d rec isK ro rc 0 major 0 0 0 rules
        hm4 hK0 hebm hmaj s₀.mem m2 _ M2 hS2 e2 ⟨rfl, hmaj, by simp, by simp, fun h => absurd rfl h⟩ hrules2
    · rw [ite_eq_right hs2, L.Arena.decBool_false_of (by simpa using hs2)]
      simp only [Bool.false_eq_true, ↓reduceIte]
      rw [← hKf]
      refine RefE.bind_callE (s₀ := ⟨m2, Locals.init []⟩) (fun _ => rfl)
        (hmtc N (hk.mono (Nat.le_succ N)) F (by omega) _ _ dn vis fe M2 eb mode d rec isK ro rc major rules
          (by omega) hS2 hm4 hebm hmaj hrules2)
        (fun hG => hG.m2c N (hk.mono (Nat.le_succ N)) (hG.knot.mono (Nat.le_succ N)) F (by omega) _ _
          dn vis fe M2 eb mode d rec isK ro rc major rules (by omega) hS2 hm4 hebm hmaj hrules2)
        fun r3 m3 c3 h3 => RefE.after_core (w := id) h3 fun M3 hS3 _ => ?_
      have e3 : erecP m3 = erecP m2 := hE.erecP_eq (by simp [iotaKeptFns]) (callW_of_callE c3)
      dsimp only [pmE.k_major_to_ctor_2]
      have h5 := list5_eta r3 h3.resOk.1
      rw [decMV_congr e2 r3, show decMV s₀.mem r3 = decMV s₀.mem [r3.headD 0, r3.tail.headD 0,
        r3.tail.tail.headD 0, r3.tail.tail.tail.headD 0, r3.tail.tail.tail.tail.headD 0] by rw [h5]]
      have hok3 := MVOk_congr e2 h3.resOk
      rw [← h5] at hok3
      have he3 : HW (r3.tail.headD 0) := by unfold HW; simpa using hok3.2.1
      exact pmJ1_ref p hp hc hw hmtc hE N hk F hnF hn62 dn vis fe eb mode d rec isK ro rc _ _ _ _ _ rules
        hm4 hK0 hebm he3 s₀.mem m3 _ M3 hS3 (e3.trans e2) hok3 (by rw [e3]; exact hrules2)

/-- **`prepare_major` refines `prepareMajor`** (`pm_ref`'s ok half). -/
theorem prepareMajor_refines' :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d rec isK ro rc major : Word) (rules : List IRecRule),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW major →
    decRules (erecP s₀.mem) ro.toNat rc.toNat = some rules →
    CoreSpec p (n + 1) "prepare_major" [mode, vis, d, rec, isK, ro, rc, major]
      (prepareMajor (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI rec)
        (isK != 0) rules (decE major)) (decMV s₀.mem) s₀ a₀ dn vis fe MM eb (MVOk s₀.mem) :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major rules hS hm4 hebm hmaj hr =>
    RefE.coreSpec (pmE_spec p hp.prepareMajor hp.prepareMajorWhnf (n + 1) s₀ mode vis d rec isK ro rc major)
      (pm_ref p hp hc hw hmtc hE n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d rec isK ro rc major
        rules hS hm4 hebm hmaj hr)

end pm

end L.Arena
