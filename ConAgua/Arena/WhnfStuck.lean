module

public import ConAgua.Arena.WhnfCoreAppLoop
public import ConAgua.Arena.ErecRdCV
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreRefine
import ConAgua.Arena.WhnfCoreProj
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import Std.Tactic.BVDecide.Normalize.BitVec
public import Std.Tactic.BVDecide.Normalize.Prop
public import Std.WP.Tactic
import all ConAgua.Arena.WhnfCore

@[expose] public section

/-!
# The stuck spine (con-ron's #556 P-A): `iota_target` and `whnf_stuck`

`iota_target(vis, h)` refines `iotaTarget` (its answer `(1, mI)` is the twin's `some (mI + 1)`),
`whnf_stuck(mode, vis, d, h, e)` refines `whnfStuck`: the spine's arguments pushed at the top
(`get_app_args`), `iota_rec_at` at the prefix `mI + 1` (the twin's `iotaRecAt … args k` reads only
`takeEidx args k`, `iotaRecAt_prefix`), the reduct re-applied (`mk_app_n_from`), the top put back.
Each over its unified model; `whnf_stuck`'s errors are `iota_rec_at`'s (`AppG`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

l_model iotaTargetE_spec (p : Prog) (hf : p.lookup "iota_target" = some iotaTargetL)
  fns [hf ↦ iotaTargetE list]
  specs [callW_spec p n "env_find", callW_spec p n "ls_node"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

l_model whnfStuckE_spec (p : Prog) (hf : p.lookup "whnf_stuck" = some whnfStuckL)
    (ht : p.lookup "iota_target" = some iotaTargetL)
  fns [hf ↦ whnfStuckE list]
  specs [iotaTargetE_spec p ht n, callW_spec p n "get_app_args", callW_spec p n "mk_app_n_from"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, ld64_rdW_specT, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## Tags off the handle word -/

/-- A tag word is one of 16. -/
theorem tagW_fin (x : Word) (hx : HW x) : ∃ k : Fin 16, tagW x = (k.val : Nat).toUInt64 :=
  ⟨⟨(tagW x).toNat, tagW_lt x hx⟩, by simp⟩

/-- `isStuckHead` off the tag mask `334` (`fvar`, `sort`, `const`, `forallE`, `lit`). -/
theorem isStuckHead_w (h : Word) (hh : HW h) :
    isStuckHead (decE h) = ((334 : Word) >>> tagW h &&& 1 != 0) := by
  simp only [isStuckHead, decE_tag h hh]
  obtain ⟨k, hk⟩ := tagW_fin h hh
  rw [hk]; clear hk; revert k; decide

/-- `whnfCoreStuckTag` off the tag mask `657` (`bvar`, `app`, `letE`, `proj`). -/
theorem stuckTag_w (e : Word) (he : HW e) :
    whnfCoreStuckTag (decE e) = ((657 : Word) >>> tagW e &&& 1 == 0) := by
  simp only [whnfCoreStuckTag, decE_tag e he]
  obtain ⟨k, hk⟩ := tagW_fin e he
  rw [hk]; clear hk; revert k; decide

/-- `whnfCoreKey` as the loop's `key` word. -/
theorem key_w (h e : Word) (hh : HW h) (he : HW e) :
    whnfCoreKey (decE h) (decE e) =
      (((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&& (1 - ((334 : Word) >>> tagW h &&& 1))) != 0) := by
  simp only [whnfCoreKey, isStuckHead, decE_tag e he, decE_tag h hh]
  obtain ⟨k, hk⟩ := tagW_fin e he
  obtain ⟨j, hj⟩ := tagW_fin h hh
  rw [hk, hj]; clear hk hj; revert k j; decide

/-- `whnfCoreCheapSafe` as the loop's `safe` word. -/
theorem safe_w (h e : Word) (hh : HW h) (he : HW e) :
    whnfCoreCheapSafe (decE h) (decE e) =
      (((128 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&&
        (((334 : Word) >>> tagW h &&& 1) ||| (if tagW h = 5 then (1 : Word) else 0))) != 0) := by
  simp only [whnfCoreCheapSafe, isStuckHead, decE_tag e he, decE_tag h hh]
  obtain ⟨k, hk⟩ := tagW_fin e he
  obtain ⟨j, hj⟩ := tagW_fin h hh
  rw [hk, hj]; clear hk hj; revert k j; decide


/-- The `key` word is a bit. -/
theorem key01 (h e : Word) (hh : HW h) (he : HW e) :
    ((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&& (1 - ((334 : Word) >>> tagW h &&& 1))) = 0 ∨
    ((640 : Word) >>> tagW e &&& 1 ||| (if tagW e = 4 then (1 : Word) else 0) &&& (1 - ((334 : Word) >>> tagW h &&& 1))) = 1 := by
  obtain ⟨k, hk⟩ := tagW_fin e he
  obtain ⟨j, hj⟩ := tagW_fin h hh
  rw [hk, hj]; clear hk hj; revert k j; decide

/-! ## The refinements -/

/-- The `viewConst` projection of a `const` handle past its view checks. -/
theorem viewConst_w (m : Mem) (a : AState) (hR : ArenaR m a) (h : Word) (hh : h.toNat < 2 ^ 32)
    (hv : viewOK m h CONST) :
    a.store.viewConst (decE h) = some (decI (tfld m CONST (tierW h) (idxW h) 0),
      decI (tfld m CONST (tierW h) (idxW h) 1)) := by
  obtain ⟨k, hk, hn, hu⟩ := node_of m a h constCS CeRecRel (·.consts) _ hR.const hv.2
  simp only [EStore.viewConst, EStore.persGetConst]
  rw [proj_tier m a hR h hh (fun t i => t.getConst i) hv.1]
  simp only [ETables.getConst, Tbl.node?, decE_idx h (narrow_of_cnt m h hR.const rfl hv.2)]
  rw [hk]
  simp [hn, hu, decI_word]

/-- `iota_target`'s answer: `(1, mI)` is `some (mI + 1)`. -/
def decTgt (r : List Word) : Option Nat :=
  if r.headD 0 = 0 then none else some ((r.tail.headD 0).toNat + 1)

/-- **`iota_target` refines `iotaTarget`** (it fails nowhere but at a dangling handle). -/
@[refines ConRon.Arena.iotaTarget]
theorem target_ref (p : Prog) (hp : WhnfCoreProg p) (G : Prop) (n : Nat) (m : Mem) (a : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (MM : ModeMaps) (eb h : Word)
    (hS : CoreS dn m a vis fe MM eb) (hh : HW h) :
    RefE G (iotaTargetE p (n + 1) m vis h) (iotaTarget fe (decE h)) a
      (CorePost decTgt dn m vis fe MM eb (fun _ => True)) := by
  have hR := hS.arena.base
  have hnone : (iotaTarget fe (decE h)).run a = .ok (none, a) →
      RefE G (.ok ([0, 0], m) : Except Err (List Word × Mem)) (iotaTarget fe (decE h)) a
        (CorePost decTgt dn m vis fe MM eb (fun _ => True)) :=
    fun hr => RefE.ret hr (CorePost.ret hS rfl trivial)
  by_cases g3 : tagW h ≠ 3
  · rw [iotaTargetE.arm1 (hc1 := g3)]
    apply hnone
    simp only [iotaTarget, decE_tag_const_beq h hh, g3, decide_false, Bool.false_eq_true, ite_false]; rfl
  have g3 : tagW h = 3 := Classical.not_not.mp g3
  by_cases c1 : tierW h ≠ 0 ∧ rdW (m.arr64 CTL) 1 = 0
  · rw [iotaTargetE.abort1 (hc1 := g3) (hc2 := c1)]; exact RefE.of_cls0 rfl
  by_cases c2 : tcnt m CONST (tierW h) ≤ idxW h
  · rw [iotaTargetE.abort2 (hc1 := g3) (hc2 := c1) (hc3 := c2)]; exact RefE.of_cls0 rfl
  rw [iotaTargetE.arm2 (hc1 := g3) (hc2 := c1) (hc3 := c2)]
  have hvo : viewOK m h CONST := ⟨c1, by simpa using c2⟩
  have hvc := viewConst_w m a hR h hh hvo
  obtain ⟨_, _, -, -, -, hw0, hw1⟩ := view_const_words m a hR h hh hvo g3
  have htw : (iotaTarget fe (decE h)).run a =
      (match fe.find? (decI (tfld m CONST (tierW h) (idxW h) 0)) with
        | some (.recInfo cv mI _ _ _) => do
          match ← viewLsLen (decI (tfld m CONST (tierW h) (idxW h) 1)) with
          | none => failDanglingLs
          | some usl => if usl = cv.levelParams.length then pure (some (mI + 1)) else pure none
        | _ => pure none : AM (Option Nat)).run a := by
    simp only [iotaTarget, decE_tag_const_beq h hh, g3, decide_true, ite_true, StateT.run_bind]
    rw [show (viewConst (decE h)).run a = .ok (a.store.viewConst (decE h), a) from rfl, hvc]
    rfl
  refine RefE.onlySim (fun _ => iotaTargetE.k_env_find.none ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨s', hs', h1', -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (envFind_refines p hp.envrow hp.baserow hp.envfind n _ vis _ hS.env hw0) h1
  have hm₁ : m = m₁ := (hs'.symm.trans h1').symm
  subst hm₁
  generalize hc0 : decI (tfld m CONST (tierW h) (idxW h) 0) = c0 at htw hfind
  by_cases f0 : r₁.headD 0 = 0
  · rw [iotaTargetE.k_env_find.arm1 (hc1 := f0)]
    apply hnone
    rw [htw]
    simp only [hfind, envFound, f0, ite_true]; rfl
  obtain ⟨ci, hci⟩ := hdec f0
  have hfind' : fe.find? c0 = some ci := by rw [hfind]; simp only [envFound, f0, ite_false]; exact hci
  by_cases k5 : erRd m (r₁.tail.headD 0) ≠ 5
  · erw [iotaTargetE.k_env_find.arm2 (hc1 := f0) (hc2 := k5)]
    have hnr := (decCI_rec_rd (erRdOK m) hci).2 k5
    apply hnone
    rw [htw, hfind']
    cases ci <;> try rfl
    exact absurd rfl (hnr _ _ _ _ _)
  have k5 : erRd m (r₁.tail.headD 0) = 5 := Classical.not_not.mp k5
  erw [iotaTargetE.k_env_find.arm3 (hc1 := f0) (hc2 := k5)]
  obtain ⟨cv, rules, rfl, hcv, -⟩ := (decCI_rec_rd (erRdOK m) hci).1 k5
  obtain ⟨-, -, -, hlen, -, -⟩ := decCV_rd1 (erRdOK m) hcv
  generalize hq : r₁.tail.headD 0 = q at *
  refine RefE.onlySim (fun _ => iotaTargetE.k_ls_node.none ..) (fun _ _ h => h) fun rl m2 c2 => ?_
  obtain ⟨t2, ht2, hs2, hne2, hr2⟩ := triple_of_callW (lsNode_spec p hp.lsn n ⟨m, Locals.init []⟩ _) c2
  have hm2 : m = m2 := by rw [← ht2, hs2]
  subst hm2
  obtain ⟨o, l, hol⟩ : ∃ o l, rl = [o, l] := by
    rcases lsNodeW_cases m (tfld m CONST (tierW h) (idxW h) 1) with h' | ⟨o, l, h'⟩
    · rw [hr2] at hne2; exact absurd h' hne2
    · exact ⟨o, l, by rw [hr2]; exact h'⟩
  have hvl := lsNodeW_viewLen hR hw1 (by rw [← hr2, hol])
  subst hol
  have hlr : (viewLsLen (decI (tfld m CONST (tierW h) (idxW h) 1))).run a = .ok (some l.toNat, a) := by
    show Except.ok (a.store.lss.viewLen _, a) = _; rw [hvl]
  by_cases u1 : [o, l].tail.headD 0 = erRd m (q + 3)
  · erw [iotaTargetE.k_ls_node.arm1 (hc1 := u1)]
    refine RefE.ret (y := some ((erRd m (q + 5)).toNat + 1)) ?_ (CorePost.ret hS (by simp [decTgt]; rfl) trivial)
    rw [htw, hfind']
    simp only [StateT.run_bind, hlr, except_ok_bind]
    simp only [List.tail_cons, List.headD_cons] at u1
    rw [ite_eq_left (by rw [hlen, u1])]; rfl
  · erw [iotaTargetE.k_ls_node.arm2 (hc1 := u1)]
    apply hnone
    rw [htw, hfind']
    simp only [StateT.run_bind, hlr, except_ok_bind]
    simp only [List.tail_cons, List.headD_cons] at u1
    rw [ite_eq_right (by rw [hlen]; exact fun h => u1 (UInt64.toNat_inj.mp h))]; rfl

/-- `eidxCopyUpto` up to `k` reads only the first `k` entries. -/
theorem eidxCopyUpto_prefix (xs : Array EIdx) (k : Nat) (hk : k ≤ xs.size) :
    ∀ (K i : Nat) (out : Array EIdx), k - i = K →
      eidxCopyUpto xs k i out = eidxCopyUpto (xs.extract 0 k) k i out := by
  intro K
  induction K with
  | zero =>
    intro i out hK
    rw [eidxCopyUpto, eidxCopyUpto]
    have : ¬ (i < k ∧ i < xs.size) := by omega
    have h2 : ¬ (i < k ∧ i < (xs.extract 0 k).size) := by simp; omega
    simp only [this, h2, dite_false]
  | succ K ih =>
    intro i out hK
    rw [eidxCopyUpto, eidxCopyUpto]
    have h1 : i < k ∧ i < xs.size := by omega
    have h2 : i < k ∧ i < (xs.extract 0 k).size := by simp; omega
    simp only [h1, h2, and_self, dite_true]
    rw [ih (i + 1) _ (by omega)]
    congr 2
    simp [Array.getElem_extract]

/-- **`iotaRecAt` reads its spine only below the arity it is asked at.** -/
theorem iotaRecAt_prefix (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd : EIdx)
    (args : Array EIdx) (k : Nat) (hk : k ≤ args.size) :
    iotaRecAt mode r fe depth hd args k = iotaRecAt mode r fe depth hd (args.extract 0 k) k := by
  have : takeEidx args k = takeEidx (args.extract 0 k) k := by
    unfold takeEidx; exact eidxCopyUpto_prefix args k hk k 0 #[] (by omega)
  simp only [iotaRecAt, this]

/-- A leading part of a stack slice. -/
theorem SpineR.prefix {m : Mem} {off cnt : Word} {xs : Array EIdx} (h : SpineR m off cnt xs)
    (c : Word) (hc : c.toNat ≤ cnt.toNat) : SpineR m off c (xs.extract 0 c.toNat) := by
  have hb := h.bound
  have hsz := h.size
  refine ⟨by simp; omega, by omega, fun i hi => h.lt i (by omega), fun i hi => ?_⟩
  have hi' : i < xs.size := by simp only [Array.size_extract] at hi; omega
  rw [Array.getElem_extract]
  simpa using h.get i hi'

section stuck
variable (p : Prog) (hp : WhnfCoreProg p) (hcc : CoreCallees p)

include hp hcc in
/-- **`whnf_stuck` refines `whnfStuck`, both outcomes**: its errors are `iota_rec_at`'s (`AppG`). -/
@[refines ConRon.Arena.whnfStuck]
theorem stuck_ref (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hF : n ≤ F) (hn : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d h e : Word) (hs : SlotPre s₀ a₀ dn vis fe MM eb mode)
    (hh : HW h) (he : HW e) :
    RefE (AppG p n) (whnfStuckE p (n + 1) s₀.mem mode vis d h e)
      (whnfStuck (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) (decE e))
      a₀ (CorePost decStep dn s₀.mem vis fe MM eb ResW) := by
  have hS := hs.rel
  rw [whnfStuckE.arm1]
  cases n with
  | zero => simp only [iotaTargetE]; exact RefE.of_cls0 rfl
  | succ N =>
  unfold whnfStuck
  refine RefE.bindE (fun _ => whnfStuckE.k_iota_target.none ..) id
    (target_ref p hp (AppG p (N + 1)) N s₀.mem a₀ dn vis fe MM eb h hS hh) fun ⟨r₁, m₁⟩ o a₁ _ hQ => ?_
  obtain ⟨M₁, hS₁, hK₁, hSt₁⟩ := hQ.after
  have hres : o = decTgt r₁ := hQ.res
  subst hres
  by_cases f0 : r₁.headD 0 = 0
  · rw [whnfStuckE.k_iota_target.arm1 (hc1 := f0)]
    simp only [decTgt, f0, ite_true]
    exact RefE.ret rfl ⟨⟨M₁, hS₁, hK₁, hSt₁⟩, by simp [decStep], ⟨show HW 0 by unfold HW; decide, he⟩⟩
  rw [whnfStuckE.k_iota_target.arm2 (hc1 := f0)]
  simp only [decTgt, f0, ite_false]
  generalize hkw : r₁.tail.headD 0 = kw
  refine RefE.onlySim (fun _ => whnfStuckE.k_get_app_args.none ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  obtain ⟨t₂, ht₂, -, hf₂, hg₂, hao, htop2, xs, hrun2, hxs⟩ := triple_of_callW
    (getAppArgs_refines p hp.spine (N + 1) ⟨m₁, Locals.init []⟩ a₁ hS₁.arena.base e he hS₁.spn) h2
  rw [ht₂] at hf₂ hg₂ htop2 hxs
  refine RefE.bind_right hrun2 ?_
  have hS₂ := hS₁.frame_stk hf₂ (by simp) (by simp)
  have htop1 : rdW (m₁.arr64 CTL) 136 = rdW (s₀.mem.arr64 CTL) 136 := hSt₁.top
  have hgrow : StackGrew s₀.mem m₂ := hSt₁.toGrew.trans hg₂
  have hdone : ∀ (m' : Mem) (a' : AState) (M' : ModeMaps), CoreS dn m' a' vis fe M' eb →
      KeptAll MM M' eb → StackGrew s₀.mem m' →
      CorePost decStep dn s₀.mem vis fe MM eb ResW ([0, e], m'.set64 CTL 136 (rdW (m₁.arr64 CTL) 136))
        (.done (decE e)) a' := fun m' a' M' hS' hK' hg' => by
    rw [htop1]
    exact (⟨⟨M', hS', hK', hg'⟩, by simp [decStep], ⟨show HW 0 by unfold HW; decide, he⟩⟩ :
      GrowPost decStep dn s₀.mem vis fe MM eb ResW ([0, e], m') (.done (decE e)) a').restore _ rfl
        ⟨show HW 0 by unfold HW; decide, he⟩
  have hsz := hxs.size
  simp only [List.size_toArray] at hsz
  by_cases hkk : ¬ kw < r₂.tail.headD 0
  · rw [whnfStuckE.k_get_app_args.arm2 (hc1 := hkk), whnfStuckE.j1.arm1]
    have : ¬ (kw.toNat + 1 ≤ xs.toArray.size) := by
      simp only [List.size_toArray, hsz]; rw [UInt64.lt_iff_toNat_lt] at hkk; omega
    simp only [this, ite_false]
    exact RefE.ret rfl (hdone _ _ _ hS₂ hK₁ hgrow)
  have hkk : kw < r₂.tail.headD 0 := Classical.not_not.mp hkk
  rw [whnfStuckE.k_get_app_args.arm1 (hc1 := hkk)]
  have hkn : kw.toNat < (r₂.tail.headD 0).toNat := UInt64.lt_iff_toNat_lt.mp hkk
  have hk1 : (kw + 1).toNat = kw.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := (r₂.tail.headD 0).toNat_lt; omega
  have hle : kw.toNat + 1 ≤ xs.toArray.size := by simp only [List.size_toArray, hsz]; omega
  simp only [hle, ite_true]
  rw [iotaRecAt_prefix _ _ _ _ _ _ _ hle]
  have hbd2 := hxs.bound
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hS₂.spn
  have htop2' : (spTop m₂).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
    rw [htop2, ← hao, L.toNat_add_of_lt _ _ (by omega)]
  have hX := hxs.prefix (kw + 1) (by rw [hk1]; omega)
  rw [hk1] at hX
  have hXs : (xs.toArray.extract 0 (kw.toNat + 1)).size = kw.toNat + 1 := by simp; omega
  generalize hXd : xs.toArray.extract 0 (kw.toNat + 1) = X at hX hXs ⊢
  rw [show iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE h) X
      (kw.toNat + 1) = iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
      (decE h) X X.size by rw [hXs]]
  have hpre : SlotPre ⟨m₂, Locals.init []⟩ a₁ dn vis fe M₁ eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => whnfStuckE.k_iota_rec_at.none ..)
    (hcc.iota N (hk.mono (by omega)) F _ a₁ dn vis fe M₁ eb mode d h _ _ X (by omega) (by omega) hpre hh hX
      (by rw [htop2', hk1]; omega))
    (fun hG => hG.iota N (hk.mono (by omega)) (hG.knot.mono (by omega)) F _ a₁ dn vis fe M₁ eb mode d h _ _ X
      (by omega) (by omega) hpre hh hX (by rw [htop2', hk1]; omega)) fun r₃ m₃ _ hI => ?_
  obtain ⟨-, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, hrw3⟩ := hI
  generalize AM.st (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
    (decE h) X X.size) a₁ = a₃ at hS₃ ⊢
  by_cases z : r₃.headD 0 = 0
  · rw [whnfStuckE.k_iota_rec_at.arm2 (hc1 := z), whnfStuckE.j1.arm1]
    have : decOptR r₃ = none := by unfold decOptR decOpt; rw [ite_eq_left z]
    rw [this]
    exact RefE.ret rfl (hdone _ _ _ hS₃ (hK₁.trans hK₃) (hgrow.trans hSt₃.toGrew))
  rw [whnfStuckE.k_iota_rec_at.arm1 (hc1 := z)]
  have : decOptR r₃ = some (decE (r₃.tail.headD 0)) := decOpt_ne _ _ z
  rw [this]
  refine RefE.onlySim (fun _ => whnfStuckE.k_mk_app_n_from.none ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  have hx3 : SpineR m₃ (r₂.headD 0) (r₂.tail.headD 0) xs.toArray :=
    hxs.keep hSt₃.size hSt₃.below (by omega) hspn₂
  obtain ⟨hok2, hD2, hres2, hfr2, hhw2⟩ := callW_mkAppNFrom p hp.spine (N + 1) ⟨m₃, Locals.init []⟩ a₃
    hS₃.arena (r₃.tail.headD 0) _ _ (kw + 1) xs.toArray hrw3.2 hx3 (by rw [hk1]; omega) r₄ m₄ h4
  have hcpl := Keeps.run (keeps_cpl_mkAppNFrom (decE (r₃.tail.headD 0)) xs.toArray (kw + 1).toNat)
    (AM.run_of_ok _ _ hok2)
  have hS₄ := hS₃.of_app hD2 hcpl hfr2
  rw [hk1] at hok2 hres2 hS₄
  have hSt4 := StackKept.of_app_frame hfr2
  rw [whnfStuckE.k_mk_app_n_from.arm1]
  have hr2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hr2
  refine RefE.ret (by simp only [StateT.run_bind, hr2, except_ok_bind]; rfl) ?_
  rw [htop1]
  exact (⟨⟨M₃, hS₄, hK₁.trans hK₃, (hgrow.trans hSt₃.toGrew).trans hSt4.toGrew⟩, by simp [decStep],
      ⟨show HW 1 by unfold HW; decide, hhw2⟩⟩ :
    GrowPost decStep dn s₀.mem vis fe MM eb ResW ([1, r₄.headD 0], m₄) _ _).restore _ rfl
      ⟨show HW 1 by unfold HW; decide, hhw2⟩

end stuck

end L.Arena
