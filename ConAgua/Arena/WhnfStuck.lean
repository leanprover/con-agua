module

public import ConAgua.Arena.WhnfCoreAppLoop
public import ConAgua.Arena.RecLayout.CIDec
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

l_model whnfStuckE_spec (p : Prog) (hf : p.lookup "whnf_stuck" = some whnfStuckL)
  fns [hf ↦ whnfStuckE list]
  specs [callW_spec p n "env_find", callW_spec p n "ls_node", callW_spec p n "get_app_args",
    callW_spec p n "mk_app_n_from"]
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

theorem eidxCopyUpto_ext (xs : Array EIdx) (k : Nat) :
    ∀ (K i : Nat) (out : Array EIdx), min k xs.size - i = K →
      eidxCopyUpto xs k i out = out ++ xs.extract i (min k xs.size) := by
  intro K
  induction K with
  | zero =>
    intro i out hK
    rw [eidxCopyUpto]
    have : ¬ (i < k ∧ i < xs.size) := by omega
    simp only [this, dite_false]
    apply Array.ext'; simp; omega
  | succ K ih =>
    intro i out hK
    rw [eidxCopyUpto]
    have h1 : i < k ∧ i < xs.size := by omega
    simp only [h1, and_self, dite_true]
    rw [ih (i + 1) _ (by omega)]
    apply Array.ext'
    simp only [Array.toList_append, Array.toList_push, Array.toList_extract, List.extract,
      List.append_assoc, List.singleton_append]
    congr 1
    have hl : i < xs.toList.length := by simpa using h1.2
    rw [List.drop_eq_getElem_cons hl, show min k xs.size - i = (min k xs.size - (i + 1)) + 1 by omega,
      List.take_succ_cons]
    simp

/-- `takeEidx` is the leading part. -/
theorem takeEidx_extract (xs : Array EIdx) (k : Nat) (hk : k ≤ xs.size) : takeEidx xs k = xs.extract 0 k := by
  unfold takeEidx
  rw [eidxCopyUpto_ext xs k _ 0 #[] rfl, Nat.min_eq_left hk]; simp

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
  have hR := hS.arena.base
  have hdone0 : ∀ (m' : Mem), m' = s₀.mem →
      CorePost decStep dn s₀.mem vis fe MM eb ResW ([0, e], m') (.done (decE e)) a₀ := fun m' hm => by
    subst hm; exact CorePost.ret hS (by simp [decStep]) ⟨show HW 0 by unfold HW; decide, he⟩
  cases n with
  | zero =>
    by_cases g3 : tagW h ≠ 3
    · simp only [whnfStuckE, g3, ne_eq, not_false_eq_true, ↓reduceIte]
      refine RefE.ret ?_ (hdone0 _ rfl)
      simp only [whnfStuck, decE_tag_const_beq h hh, show ¬ tagW h = 3 from g3, decide_false,
        Bool.false_eq_true, ↓reduceIte]; rfl
    · have g3' : tagW h = 3 := by simpa using g3
      simp only [whnfStuckE, g3', ne_eq, not_true_eq_false, ↓reduceIte]
      refine RefE.abort0 (by decide) fun _ => RefE.abort0 (by decide) fun _ => ?_
      rw [callW_zero, liftE_none, whnfStuckE.k_env_find.eq_1]; exact RefE.of_cls0 (by simp)
  | succ N =>
  unfold whnfStuck
  by_cases g3 : tagW h ≠ 3
  · simp only [whnfStuckE, g3, ne_eq, not_false_eq_true, ↓reduceIte]
    refine RefE.ret ?_ (hdone0 _ rfl)
    simp only [decE_tag_const_beq h hh, show ¬ tagW h = 3 from g3, decide_false,
      Bool.false_eq_true, ↓reduceIte]; rfl
  have g3' : tagW h = 3 := by simpa using g3
  simp only [whnfStuckE, g3', ne_eq, not_true_eq_false, ↓reduceIte]
  refine RefE.abort0 (by decide) fun c1 => ?_
  refine RefE.abort0 (by decide) fun c2 => ?_
  have hvo : viewOK s₀.mem h CONST := ⟨c1, by simpa using c2⟩
  have hvc := viewConst_w s₀.mem a₀ hR h hh hvo
  obtain ⟨_, _, -, -, -, hw0, hw1⟩ := view_const_words s₀.mem a₀ hR h hh hvo g3'
  simp only [decE_tag_const_beq h hh, g3', decide_true, ↓reduceIte]
  refine RefE.bind_right (show (viewConst (decE h)).run a₀ = .ok (_, a₀) from rfl) ?_
  rw [hvc]
  dsimp only
  generalize hc0 : tfld s₀.mem CONST (tierW h) (idxW h) 0 = cw at hw0 ⊢
  generalize hu0 : tfld s₀.mem CONST (tierW h) (idxW h) 1 = uw at hw1 ⊢
  refine RefE.onlySim (fun _ => whnfStuckE.k_env_find.eq_1 ..) (fun _ _ h => h) fun r₁ m₁ h1 => ?_
  obtain ⟨s', hs', h1', -, hfind, hdec⟩ := triple_of_callW (s₀ := ⟨s₀.mem, Locals.init []⟩)
    (envFind_refines p hp.envrow hp.baserow hp.envfind (N + 1) _ vis _ hS.env hw0) h1
  have hm₁ : s₀.mem = m₁ := (hs'.symm.trans h1').symm
  subst hm₁
  dsimp only [whnfStuckE.k_env_find]
  by_cases f0 : r₁.headD 0 = 0
  · rw [ite_eq_left f0]
    have hn : fe.find? (decI cw) = none := by rw [hfind]; simp only [envFound, f0, ↓reduceIte]
    rw [hn]; exact RefE.ret rfl (hdone0 _ rfl)
  rw [ite_eq_right f0]
  obtain ⟨ci, hci⟩ := hdec f0
  have hfind' : fe.find? (decI cw) = some ci := by
    rw [hfind]; simp only [envFound, f0, ↓reduceIte]; exact hci
  rw [hfind']
  by_cases k5 : erRd s₀.mem (r₁.tail.headD 0) ≠ 5
  · erw [ite_eq_left k5]
    have hnr := (decCI_rec_rd (erRdOK s₀.mem) hci).2 k5
    cases ci <;> first | exact absurd rfl (hnr _ _ _ _ _) | exact RefE.ret rfl (hdone0 _ rfl)
  have k5 : erRd s₀.mem (r₁.tail.headD 0) = 5 := Classical.not_not.mp k5
  erw [ite_eq_right (by simpa [erRd] using k5)]
  obtain ⟨cv, rules, rfl, hcv, -⟩ := (decCI_rec_rd (erRdOK s₀.mem) hci).1 k5
  obtain ⟨-, -, -, hlen, -, -⟩ := decCV_rd_ci (erRdOK s₀.mem) hcv
  generalize hq : r₁.tail.headD 0 = q at *
  dsimp only
  refine RefE.onlySim (fun _ => whnfStuckE.k_ls_node.eq_1 ..) (fun _ _ h => h) fun rl m2 c2 => ?_
  obtain ⟨t2, ht2, hs2, hne2, hr2⟩ := triple_of_callW (lsNode_spec p hp.lsn (N + 1) ⟨s₀.mem, Locals.init []⟩ _) c2
  have hm2 : s₀.mem = m2 := by rw [← ht2, hs2]
  subst hm2
  obtain ⟨o, l, hol⟩ : ∃ o l, rl = [o, l] := by
    rcases lsNodeW_cases s₀.mem uw with h' | ⟨o, l, h'⟩
    · rw [hr2] at hne2; exact absurd h' hne2
    · exact ⟨o, l, by rw [hr2]; exact h'⟩
  have hvl := lsNodeW_viewLen hR hw1 (by rw [← hr2, hol])
  subst hol
  have hlr : (viewLsLen (decI uw)).run a₀ = .ok (some l.toNat, a₀) := by
    show Except.ok (a₀.store.lss.viewLen _, a₀) = _; rw [hvl]
  refine RefE.bind_right hlr ?_
  dsimp only [whnfStuckE.k_ls_node]
  simp only [List.tail_cons, List.headD_cons]
  by_cases u1 : l ≠ erRd s₀.mem (q + (CI.cv + CV.lpsLen))
  · erw [ite_eq_left (by simpa [erRd] using u1)]
    rw [ite_eq_left (by rw [hlen]; exact fun h => u1 (UInt64.toNat_inj.mp h))]
    exact RefE.ret rfl (hdone0 _ rfl)
  have u1 : l = erRd s₀.mem (q + (CI.cv + CV.lpsLen)) := Classical.not_not.mp u1
  erw [ite_eq_right (by simpa [erRd] using u1)]
  rw [ite_eq_right (by rw [hlen, u1]; exact fun h => h rfl)]
  generalize hkw : erRd s₀.mem (q + CI.recMajor) = kw at *
  refine RefE.onlySim (fun _ => whnfStuckE.k_get_app_args.eq_1 ..) (fun _ _ h => h) fun r₂ m₂ h2 => ?_
  obtain ⟨t₂, ht₂, -, hf₂, hg₂, hao, htop2, xs, hrun2, hxs⟩ := triple_of_callW
    (getAppArgs_refines p hp.spine (N + 1) ⟨s₀.mem, Locals.init []⟩ a₀ hR e he hS.spn) h2
  rw [ht₂] at hf₂ hg₂ htop2 hxs
  refine RefE.bind_right hrun2 ?_
  have hS₂ := hS.frame_stk hf₂ (by simp) (by simp)
  have hE2 : m₂.arr64 EREC = s₀.mem.arr64 EREC := hf₂.arr EREC (by simp [EREC, SPN]) (by decide)
  have hE2t : m₂.arr64 (tier1 EREC) = s₀.mem.arr64 (tier1 EREC) :=
    hf₂.arr (tier1 EREC) (by simp [tier1, EREC, SPN]) (by decide)
  have hEp : erecP m₂ = erecP s₀.mem := erecP_frame hf₂ (by decide) (by decide) (by decide) (by decide)
  dsimp only [whnfStuckE.k_get_app_args]
  simp only [erRd_congr hE2 hE2t, hkw]
  have hgrow : StackGrew s₀.mem m₂ := hg₂
  have hdone : ∀ (m' : Mem) (a' : AState) (M' : ModeMaps), CoreS dn m' a' vis fe M' eb →
      KeptAll MM M' eb → StackGrew s₀.mem m' →
      CorePost decStep dn s₀.mem vis fe MM eb ResW ([0, e], m'.set64 CTL 136 (rdW (s₀.mem.arr64 CTL) 136))
        (.done (decE e)) a' := fun m' a' M' hS' hK' hg' =>
    (⟨⟨M', hS', hK', hg'⟩, by simp [decStep], ⟨show HW 0 by unfold HW; decide, he⟩⟩ :
      GrowPost decStep dn s₀.mem vis fe MM eb ResW ([0, e], m') (.done (decE e)) a').restore _ rfl
        ⟨show HW 0 by unfold HW; decide, he⟩
  have hsz := hxs.size
  simp only [List.size_toArray] at hsz
  by_cases hkk : ¬ kw < r₂.tail.headD 0
  · rw [ite_eq_right hkk, whnfStuckE.j1.arm1]
    have : ¬ (kw.toNat + 1 ≤ xs.toArray.size) := by
      simp only [List.size_toArray, hsz]; rw [UInt64.lt_iff_toNat_lt] at hkk; omega
    simp only [this, ite_false]
    exact RefE.ret rfl (hdone _ _ _ hS₂ (KeptAll.refl _ _) hgrow)
  have hkk : kw < r₂.tail.headD 0 := Classical.not_not.mp hkk
  rw [ite_eq_left hkk]
  have hkn : kw.toNat < (r₂.tail.headD 0).toNat := UInt64.lt_iff_toNat_lt.mp hkk
  have hk1 : (kw + 1).toNat = kw.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; have := (r₂.tail.headD 0).toNat_lt; omega
  have hle : kw.toNat + 1 ≤ xs.toArray.size := by simp only [List.size_toArray, hsz]; omega
  simp only [hle, ite_true]
  rw [takeEidx_extract _ _ hle]
  have hbd2 := hxs.bound
  have hspn₂ : (m₂.arr64 SPN).size < 2 ^ 63 := hS₂.spn
  have htop2' : (spTop m₂).toNat = (r₂.headD 0).toNat + (r₂.tail.headD 0).toNat := by
    rw [htop2, ← hao, L.toNat_add_of_lt _ _ (by omega)]
  have hX := hxs.prefix (kw + 1) (by rw [hk1]; omega)
  rw [hk1] at hX
  have hXs : (xs.toArray.extract 0 (kw.toNat + 1)).size = kw.toNat + 1 := by simp; omega
  generalize hXd : xs.toArray.extract 0 (kw.toNat + 1) = X at hX hXs ⊢
  have hpre : SlotPre ⟨m₂, Locals.init []⟩ a₀ dn vis fe MM eb mode := ⟨hS₂, hs.mode4, hs.eb_mode⟩
  have hq2 : decCI (erecP m₂) q.toNat = some (.recInfo cv kw.toNat (erRd s₀.mem (q + CI.recPrefix)).toNat
      (erRd s₀.mem (q + CI.recIsK) != 0) rules) := by rw [hEp]; exact hci
  have hf2 : fe.find? (decI cw) = some (.recInfo cv kw.toNat (erRd s₀.mem (q + CI.recPrefix)).toNat
      (erRd s₀.mem (q + CI.recIsK) != 0) rules) := hfind'
  refine RefE.bind_callE (s₀ := ⟨m₂, Locals.init []⟩) (fun _ => whnfStuckE.k_iota_rec_at.eq_1 ..)
    (hcc.iota N (hk.mono (by omega)) F _ a₀ dn vis fe MM eb mode d cw uw q _ _ X cv _ _ _ rules (by omega)
      (by omega) hpre hw0 hw1 hq2 hf2 hX hXs (by rw [htop2', hk1]; omega))
    (fun hG => hG.iota N (hk.mono (by omega)) (hG.knot.mono (by omega)) F _ a₀ dn vis fe MM eb mode d cw uw q
      _ _ X cv _ _ _ rules (by omega) (by omega) hpre hw0 hw1 hq2 hf2 hX hXs (by rw [htop2', hk1]; omega))
    fun r₃ m₃ _ hI => ?_
  obtain ⟨-, ⟨M₃, hS₃, hK₃, hSt₃⟩, -, hrw3⟩ := hI
  generalize AM.st (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat
    (decI cw) (decI uw) cv kw.toNat (erRd s₀.mem (q + CI.recPrefix)).toNat (erRd s₀.mem (q + CI.recIsK) != 0)
    rules X) a₀ = a₃ at hS₃ ⊢
  by_cases z : r₃.headD 0 = 0
  · rw [whnfStuckE.k_iota_rec_at.arm2 (hc1 := z), whnfStuckE.j1.arm1]
    have : decOptR r₃ = none := by unfold decOptR decOpt; rw [ite_eq_left z]
    rw [this]
    exact RefE.ret rfl (hdone _ _ _ hS₃ hK₃ (hgrow.trans hSt₃.toGrew))
  rw [whnfStuckE.k_iota_rec_at.arm1 (hc1 := z)]
  have : decOptR r₃ = some (decE (r₃.tail.headD 0)) := decOpt_ne _ _ z
  rw [this]
  refine RefE.onlySim (fun _ => whnfStuckE.k_mk_app_n_from.eq_1 ..) (fun _ _ h => h) fun r₄ m₄ h4 => ?_
  have hx3 : SpineR m₃ (r₂.headD 0) (r₂.tail.headD 0) xs.toArray :=
    hxs.keep hSt₃.size hSt₃.below (by omega) hspn₂
  obtain ⟨hok2, hD2, hres2, hfr2, hhw2⟩ := callW_mkAppNFrom p hp.spine (N + 1) ⟨m₃, Locals.init []⟩ a₃
    hS₃.arena (r₃.tail.headD 0) _ _ (kw + 1) xs.toArray hrw3.2 hx3 (by rw [hk1]; omega) r₄ m₄ h4
  have hcpl := Keeps.run (keeps_cpl_mkAppNFrom (decE (r₃.tail.headD 0)) xs.toArray (kw + 1).toNat)
    (AM.run_of_ok _ _ hok2)
  have hS₄ := hS₃.of_app hD2 hcpl hfr2
  rw [hk1] at hok2 hres2 hS₄
  have hSt4 := StackKept.of_app_frame hfr2
  dsimp only [whnfStuckE.k_mk_app_n_from]
  have hr2 := AM.run_of_ok _ _ hok2
  rw [hres2] at hr2
  refine RefE.ret (by simp only [StateT.run_bind, hr2, except_ok_bind]; rfl) ?_
  exact (⟨⟨M₃, hS₄, hK₃, (hgrow.trans hSt₃.toGrew).trans hSt4.toGrew⟩, by simp [decStep],
      ⟨show HW 1 by unfold HW; decide, hhw2⟩⟩ :
    GrowPost decStep dn s₀.mem vis fe MM eb ResW ([1, r₄.headD 0], m₄) _ _).restore _ rfl
      ⟨show HW 1 by unfold HW; decide, hhw2⟩

end stuck

end L.Arena
