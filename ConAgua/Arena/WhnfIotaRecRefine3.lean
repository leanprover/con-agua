module

public import ConAgua.Arena.WhnfIotaRecRefine2
public import ConAgua.Arena.GrindAttr
import ConAgua.Arena.IndPosSpec.NestBlockOfKey
import ConAgua.Arena.RefWalk
import ConAgua.Arena.WhnfCoreProj
import ConRon.Bridge.Grind
import ConAgua.Arena.RecLayout.CIDec

@[expose] public section

/-!
# `iota_rec_at`'s pieces, part 3: the recursor's block and the top

`iota_rec_c` (the recursor's record, the arity, the level-list length, the telescope) and
`iota_rec_at` itself: `iotaRecAt_refines'` proves `WhnfCore.lean`'s `IotaRecAtOK` from the
callees' specs and the stub assumption `ErecKeptRec`; the
census-tagged `iotaRecAt_refines` instantiates them.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

/-! ## `takeEidx` at the whole array -/

theorem eidxCopyUpto_size (xs : Array EIdx) : ∀ (K i : Nat) (out : Array EIdx), xs.size - i = K →
    i ≤ xs.size → eidxCopyUpto xs xs.size i out = out ++ xs.extract i xs.size := by
  intro K
  induction K with
  | zero =>
    intro i out hK hi
    have : i = xs.size := by omega
    subst this
    rw [eidxCopyUpto]
    simp
  | succ K ih =>
    intro i out hK hi
    rw [eidxCopyUpto]
    have hlt : i < xs.size := by omega
    simp only [hlt, and_self, ↓reduceDIte]
    rw [ih (i + 1) _ (by omega) (by omega)]
    apply Array.ext'
    simp only [Array.toList_append, Array.toList_push, Array.toList_extract, List.extract,
      List.append_assoc, List.singleton_append]
    congr 1
    have hl : i < xs.toList.length := by simpa using hlt
    rw [List.drop_eq_getElem_cons hl, show xs.size - i = (xs.size - (i + 1)) + 1 by omega,
      List.take_succ_cons]
    simp

theorem takeEidx_size (xs : Array EIdx) : takeEidx xs xs.size = xs := by
  unfold takeEidx
  rw [eidxCopyUpto_size xs xs.size 0 #[] (by omega) (by omega)]
  simp

/-! ## `iota_rec_c(mode, vis, d, c, us, so, sn)` -/

section cRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
  (us : LsIdx) (sargs : Array EIdx) (n : Nat)

theorem cT_run_find (a : AState) (hf : ∀ cv mI rP isK rules, fe.find? c ≠ some (.recInfo cv mI rP isK rules)) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  unfold iotaRecCT
  cases h : fe.find? c with
  | none => rfl
  | some ci =>
    cases ci with
    | recInfo cv mI rP isK rules => exact absurd h (hf cv mI rP isK rules)
    | _ => rfl

theorem cT_run_arity (a : AState) (cv : IConstantVal) (mI rP : Nat) (isK : Bool) (rules : List IRecRule)
    (hf : fe.find? c = some (.recInfo cv mI rP isK rules)) (hn : n ≠ mI + 1) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  simp only [iotaRecCT, hf, hn, ne_eq, not_false_eq_true, ↓reduceIte]; rfl

theorem cT_run_check (a : AState) (cv : IConstantVal) (mI rP : Nat) (isK : Bool) (rules : List IRecRule)
    (usl : Nat) (pe : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP isK rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : ¬ ((takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true)) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  subst hn
  simp only [iotaRecCT, hf, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_bind,
    viewLsLen_run, hl, except_ok_bind, hp]
  rw [ite_eq_right hc]; rfl

theorem cT_eq_major (a : AState) (cv : IConstantVal) (mI rP : Nat) (isK : Bool) (rules : List IRecRule)
    (usl : Nat) (pe : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP isK rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : (takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true) :
    (iotaRecCT mode r fe depth c us sargs n).run a =
      (iotaRecMajorT mode r fe depth c us cv mI rP isK rules (takeEidx sargs n).toList).run a := by
  subst hn
  simp only [iotaRecCT, hf, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_bind,
    viewLsLen_run, hl, except_ok_bind, hp]
  rw [ite_eq_left hc]

end cRun

/-- **`iota_rec_c` refines the recursor's block, both outcomes**: the errors are
`iota_rec_major`'s. -/
theorem c_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us so sn : Word) (xs : Array EIdx)
    (hS : CoreS dn s₀.mem a₀ vis fe MM eb) (hm4 : mode < 4) (hebm : eb = (mode >>> 1) &&& 1)
    (hcw : HW c) (hus : HW us) (hsa : SpineR s₀.mem so sn xs)
    (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (MajorG p n) (irCE p (n + 1) s₀.mem mode vis d c us so sn)
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) := by
  simp only [irCE]
  have hspn := hS.spn
  have herec := hS.erec
  have hsz : xs.size = sn.toNat := hsa.size
  have hnone : ∀ (m : Mem), m = s₀.mem →
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size).run a₀ = .ok (none, a₀) →
      RefE (MajorG p n) (.ok ([0, 0], m) : Except Err (List Word × Mem))
        (iotaRecCT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us)
          xs xs.size) a₀ (CorePost decOptR dn s₀.mem vis fe MM eb ResW) :=
    fun m hm hrunT => by
      subst hm
      exact RefE.ret hrunT (CorePost.ret hS rfl
        ⟨by show HW (0 : Word); unfold HW; decide, by show HW (0 : Word); unfold HW; decide⟩)
  -- the recursor's record
  refine RefE.onlySim (fun _ => irCE.k_env_find.none ..) (fun _ _ h => h) fun re m1 c1 => ?_
  obtain ⟨hm1, hfnone, hfsome⟩ := irEnvFind p hp.toIotaProg' n dn s₀.mem vis fe hS.env c hcw re m1 c1
  subst m1
  simp only [irCE.k_env_find]
  by_cases f0 : re.headD 0 = 0
  · rw [ite_eq_left f0]
    exact hnone _ rfl (cT_run_find _ _ _ _ _ _ _ _ a₀ (fun _ _ _ _ _ h => by
      rw [hfnone f0] at h; cases h))
  rw [ite_eq_right f0]
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  by_cases k5 : erRd s₀.mem (re.tail.headD 0) ≠ 5
  · erw [ite_eq_left k5]
    have hnr := (decCI_rec_rd (erRdOK s₀.mem) hci).2 k5
    exact hnone _ rfl (cT_run_find _ _ _ _ _ _ _ _ a₀ (fun cv mI rP isK rules h => by
      rw [hfind] at h; cases h; exact hnr cv mI rP isK rules rfl))
  erw [ite_eq_right k5]
  obtain ⟨cv, rules, rfl, hcv, hrules⟩ := (decCI_rec_rd (erRdOK s₀.mem) hci).1 (Classical.not_not.mp k5)
  generalize hrecP : re.tail.headD 0 = recP at *
  -- the arity
  have hmIw := (erRd s₀.mem (recP + 5)).toNat_lt
  by_cases s0 : sn = 0
  · rw [ite_eq_left s0]
    exact hnone _ rfl (cT_run_arity _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ hfind (by rw [hsz, s0]; simp))
  rw [ite_eq_right s0]
  have hsn1 : (sn - 1).toNat = sn.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      have : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
      rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hsnp : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
  by_cases a1 : sn - 1 ≠ erRd s₀.mem (recP + 5)
  · erw [ite_eq_left a1]
    exact hnone _ rfl (cT_run_arity _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ hfind (by
      rw [hsz]; intro h; apply a1; apply UInt64.toNat_inj.mp; rw [hsn1]; omega))
  erw [ite_eq_right a1]
  have hn : xs.size = (erRd s₀.mem (recP + 5)).toNat + 1 := by
    have := congrArg UInt64.toNat (Classical.not_not.mp a1); rw [hsn1] at this; omega
  -- the levels' length and the telescope
  obtain ⟨-, hname, hlps, hlen, htyw, htype⟩ := decCV_rd_ci (erRdOK s₀.mem) hcv
  refine RefE.onlySim (fun _ => irCE.k_ls_node.none ..) (fun _ _ h => h) fun rl m2 c2 => ?_
  obtain ⟨t2, ht2, hs2, hne2, hr2⟩ := triple_of_callW (lsNode_spec p hp.lvl.lsnode n
    ⟨s₀.mem, Locals.init []⟩ us) c2
  have hm2 : m2 = s₀.mem := by rw [← ht2, hs2]
  subst hm2
  obtain ⟨o, l, hol⟩ : ∃ o l, rl = [o, l] := by
    rcases lsNodeW_cases s₀.mem us with h | ⟨o, l, h⟩
    · rw [hr2] at hne2; exact absurd h hne2
    · exact ⟨o, l, by rw [hr2]; exact h⟩
  have hvl := lsNodeW_viewLen hS.arena.base hus (by rw [← hr2, hol])
  subst hol
  simp only [irCE.k_ls_node]
  refine RefE.onlySim (fun _ => irCE.k_peel_pis.none ..) (fun _ _ h => h) fun rp m3 c3 => ?_
  obtain ⟨t3, ht3, hm3, -, -, hrunP⟩ := triple_of_callW
    (peelPis_refines' p hp.spine.peel n ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.base sn _ htyw) c3
  have hm3' : s₀.mem = m3 := hm3.symm.trans ht3
  subst hm3'
  simp only [irCE.k_peel_pis]
  have hrunP' : (peelPis ((erRd s₀.mem (recP + 5)).toNat + 1) cv.type).run a₀ =
      .ok (decOpt (rp.headD 0) (rp.tail.headD 0), a₀) := by
    rw [htype, ← hn, hsz]; exact hrunP
  have htk : (takeEidx xs xs.size).toList.length = (erRd s₀.mem (recP + 5)).toNat + 1 := by
    rw [takeEidx_size]; simp [hn]
  by_cases u1 : [o, l].tail.headD 0 ≠ erRd s₀.mem (recP + 3)
  · erw [ite_eq_left u1]
    exact hnone _ rfl (cT_run_check _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _ _ hfind hn hvl hrunP'
      (fun ⟨_, h2, _⟩ => u1 (by rw [hlen] at h2; exact UInt64.toNat_inj.mp h2)))
  erw [ite_eq_right u1]
  by_cases p0 : rp.headD 0 = 0
  · rw [ite_eq_left p0]
    exact hnone _ rfl (cT_run_check _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _ _ hfind hn hvl hrunP'
      (fun ⟨_, _, h3⟩ => by rw [p0] at h3; simp [decOpt] at h3))
  rw [ite_eq_right p0]
  -- the major
  have hcnd : (takeEidx xs xs.size).toList.length = (erRd s₀.mem (recP + 5)).toNat + 1 ∧
      UInt64.toNat ([o, l].tail.headD 0) = cv.levelParams.length ∧
      (decOpt (rp.headD 0) (rp.tail.headD 0)).isSome = true := by
    refine ⟨htk, ?_, by unfold decOpt; rw [ite_eq_right p0]; rfl⟩
    rw [hlen]; have := Classical.not_not.mp u1; simp only [List.tail_cons, List.headD_cons] at this
    rw [this]; rfl
  have hT := (cT_eq_major (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c)
    (decI us) xs xs.size a₀ cv _ _ _ rules _ _ hfind hn hvl hrunP' hcnd).trans
    (by rw [takeEidx_size])
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  have hM := major_ref p hp hc hw hsup hmtc hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega)
    s₀ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS hm4 hebm hcw hus
    hcv hrules ⟨_, _, _, _, hfind⟩ hsa hsat (by omega)
  exact RefE.tail_eq (k := irCE.k_iota_rec_major p) (G' := MajorG p N)
    (fun _ => rfl) (fun _ => rfl) (fun hG => ⟨hG.knot.mono (Nat.le_succ N), hG.nv, hG.pm, hG.fire⟩) hT
    (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩) hM

/-- **`iota_rec_c` refines the recursor's block** (`c_ref`'s ok half). -/
theorem iotaRecC_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us so sn : Word) (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "iota_rec_c" [mode, vis, d, c, us, so, sn]
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size) decOptR s₀ a₀ dn vis fe MM eb ResW :=
  fun n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us so sn xs hS hm4 hebm hcw hus hsa hsat =>
    RefE.coreSpec (irCE_spec p hp.recC hp.major (n + 1) s₀ mode vis d c us so sn)
      (c_ref p hp hc hw hsup hmtc hEI hER hEK n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us so sn xs
        hS hm4 hebm hcw hus hsa hsat)

/-! ## `iota_rec_at(mode, vis, d, hd, so, sn)` -/

section atRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd : EIdx)
  (sargs : Array EIdx) (n : Nat)

theorem at_run_tag (a : AState) (ht : hd.tag ≠ ETag.const) :
    (iotaRecAt mode r fe depth hd sargs n).run a = .ok (none, a) := by
  have : (hd.tag == ETag.const) = false := by simpa using ht
  rw [iotaRecAt_eq]; simp only [this, Bool.false_eq_true, ↓reduceIte]; rfl

theorem at_eq_c (a : AState) (c : NIdx) (us : LsIdx)
    (ht : hd.tag = ETag.const) (hv : a.store.viewConst hd = some (c, us)) :
    (iotaRecAt mode r fe depth hd sargs n).run a = (iotaRecCT mode r fe depth c us sargs n).run a := by
  have hvr : (viewConst hd).run a = .ok (some (c, us), a) := by
    show Except.ok (a.store.viewConst hd, a) = _; rw [hv]
  rw [iotaRecAt_eq]
  simp only [ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hvr, except_ok_bind]

end atRun

/-- **`iota_rec_at` refines `iotaRecAt`, both outcomes**: the errors are `iota_rec_c`'s. -/
theorem at_ref (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) (F : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (M : ModeMaps)
    (eb mode d hd so sn : Word) (xs : Array EIdx) (hnF : n ≤ F) (hn62 : n ≤ 2 ^ 62)
    (hpre : SlotPre s₀ a₀ dn vis fe M eb mode) (hhd : HW hd) (hsa : SpineR s₀.mem so sn xs)
    (hsat : so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat) :
    RefE (MajorG p n) (irAtE p (n + 1) s₀.mem mode vis d hd so sn)
      (iotaRecAt (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) xs xs.size) a₀
      (CorePost decOptR dn s₀.mem vis fe M eb ResW) := by
  have hS := hpre.rel
  simp only [irAtE]
  refine RefE.onlySim (fun _ => irAtE.k_iota_rec_head.none ..) (fun _ _ h => h) fun rv m1 c1 => ?_
  obtain ⟨hm1, hnot, hyes⟩ := irCallW_head p hp.head n s₀.mem a₀ hS.arena.base hd hhd rv m1 c1
  subst m1
  simp only [irAtE.k_iota_rec_head]
  by_cases v0 : rv.headD 0 = 0
  · rw [ite_eq_left v0]
    exact RefE.ret (at_run_tag (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) xs
      xs.size a₀ (hnot v0)) (CorePost.ret hS rfl
        ⟨by show HW (0 : Word); unfold HW; decide, by show HW (0 : Word); unfold HW; decide⟩)
  rw [ite_eq_right v0]
  obtain ⟨htag, hview, hcw, husw⟩ := hyes v0
  have hvc := L.Ind.EStore.viewConst_of_view _ _ htag _ _ hview
  cases n with
  | zero => exact RefE.of_cls0 (e := .outOfFuel) rfl
  | succ N =>
  exact RefE.tail_eq (k := irAtE.k_iota_rec_c p) (G' := MajorG p N)
    (fun _ => rfl) (fun _ => rfl) (fun hG => ⟨hG.knot.mono (Nat.le_succ N), hG.nv, hG.pm, hG.fire⟩)
    (at_eq_c (decMode mode) (coreKnot (decMode mode) (decEager mode) fe id F) fe d.toNat (decE hd) xs xs.size a₀ _ _
      htag hvc) (fun _ _ _ h => ⟨h.after, h.res, h.valid⟩)
    (c_ref p hp hc hw hsup hmtc hEI hER hEK N (hk.mono (by omega)) F (by omega) (by omega) s₀ a₀ dn vis
      fe M eb mode d _ _ so sn xs hS hpre.mode4 hpre.eb_mode hcw husw hsa hsat)

/-- **`iota_rec_at` refines `iotaRecAt`** (`IotaRecAtOK`, what `whnf_app` assumes; `at_ref`'s ok
half), from the callees' specs and the stub assumption `ErecKeptRec` (the callees the pieces read
the record pool after leave it alone). -/
theorem iotaRecAt_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) :=
  fun F s₀ a₀ dn vis fe M eb mode d hd so sn xs hnF hn62 hpre hhd hsa hsat =>
    RefE.coreSpec (irAtE_spec p hp.iotaRecAt hp.recC hp.major (n + 1) s₀ mode vis d hd so sn)
      (at_ref p hp hc hw hsup hmtc hEI hER hEK n hk F s₀ a₀ dn vis fe M eb mode d hd so sn xs
        (by omega) (by omega) hpre hhd hsa hsat)

end L.Arena
