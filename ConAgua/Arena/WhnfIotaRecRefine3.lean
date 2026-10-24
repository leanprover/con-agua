import ConAgua.Arena.WhnfIotaRecRefine2
import ConAgua.Arena.WhnfM2CRefine5

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
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

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

/-- Model of `iota_rec_c` past the arity. -/
def irCTail (p : Prog) (n : Nat) (m : Mem) (mode vis d c us so sn recP : Word) :
    Option (Word × Word × Mem) :=
  match callW p n "ls_node" [us] m with
  | none => none
  | some (rl, m2) =>
  match callW p n "peel_pis" [sn, rdW (m2.arr64 EREC) (recP + 4)] m2 with
  | none => none
  | some (rp, m3) =>
  if rl.tail.headD 0 ≠ rdW (m3.arr64 EREC) (recP + 3) then some (0, 0, m3) else
  if rp.headD 0 = 0 then some (0, 0, m3) else
  match callW p n "iota_rec_major" [mode, vis, d, c, us, recP, so, sn] m3 with
  | none => none
  | some (rr, m4) => some (rr.headD 0, rr.tail.headD 0, m4)

/-- Model of `iota_rec_c`. -/
def irCW (p : Prog) (n : Nat) (m : Mem) (mode vis d c us so sn : Word) : Option (Word × Word × Mem) :=
  match callW p n "env_find" [c, vis] m with
  | none => none
  | some (re, m1) =>
  if re.headD 0 = 0 then some (0, 0, m1) else
  if rdW (m1.arr64 EREC) (re.tail.headD 0) ≠ 5 then some (0, 0, m1) else
  if sn = 0 then some (0, 0, m1) else
  if sn - 1 ≠ rdW (m1.arr64 EREC) (re.tail.headD 0 + 5) then some (0, 0, m1) else
  irCTail p n m1 mode vis d c us so sn (re.tail.headD 0)

theorem iotaRecC_spec (p : Prog) (hp : p.lookup "iota_rec_c" = some iotaRecCL) (n : Nat) (s₀ : St)
    (mode vis d c us so sn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_c" [mode, vis, d, c, us, so, sn]
    ⦃fun r s' => LocEq s' s₀ ∧ irCW p n s₀.mem mode vis d c us so sn =
      some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecCL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "env_find", callW_spec p n "ls_node", callW_spec p n "peel_pis",
    callW_spec p n "iota_rec_major"] <;>
  simp_all [-UInt64.toNat_add, irCW, irCTail, EREC, BinOp.eval, getElem_rdW', Cmp.eval, LocEq,
    St.setLocs_cons, St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, Locals.init_cons_zero,
    Locals.init_cons_succ, Sig.retVal, Sig.retOr]

section cRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx)
  (us : LsIdx) (sargs : Array EIdx) (n : Nat)

theorem cT_run_find (a : AState) (hf : ∀ cv mI rP rules, fe.find? c ≠ some (.recInfo cv mI rP rules)) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  unfold iotaRecCT
  cases h : fe.find? c with
  | none => rfl
  | some ci =>
    cases ci with
    | recInfo cv mI rP rules => exact absurd h (hf cv mI rP rules)
    | _ => rfl

theorem cT_run_arity (a : AState) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n ≠ mI + 1) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  simp only [iotaRecCT, hf, hn, ne_eq, not_false_eq_true, ↓reduceIte]; rfl

theorem cT_run_check (a : AState) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule)
    (usl : Nat) (pe : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : ¬ ((takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true)) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (none, a) := by
  subst hn
  simp only [iotaRecCT, hf, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_bind,
    viewLsLen_run, hl, except_ok_bind, hp]
  rw [if_neg hc]; rfl

theorem cT_run_major (a a' : AState) (cv : IConstantVal) (mI rP : Nat) (rules : List IRecRule)
    (usl : Nat) (pe : Option EIdx) (res : Option EIdx)
    (hf : fe.find? c = some (.recInfo cv mI rP rules)) (hn : n = mI + 1)
    (hl : a.store.lss.viewLen us = some usl) (hp : (peelPis (mI + 1) cv.type).run a = .ok (pe, a))
    (hc : (takeEidx sargs n).toList.length = mI + 1 ∧ usl = cv.levelParams.length ∧
      pe.isSome = true)
    (hm : (iotaRecMajorT mode r fe depth c us cv mI rP rules (takeEidx sargs n).toList).run a =
      .ok (res, a')) :
    (iotaRecCT mode r fe depth c us sargs n).run a = .ok (res, a') := by
  subst hn
  simp only [iotaRecCT, hf, ne_eq, not_true_eq_false, ↓reduceIte, StateT.run_bind,
    viewLsLen_run, hl, except_ok_bind, hp]
  rw [if_pos hc]; exact hm

end cRun

/-- **`iota_rec_c` refines the recursor's block.** -/
theorem iotaRecC_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p) :
    ∀ (n : Nat), KnotUpTo p n → ∀ (F : Nat), n ≤ F → n ≤ 2 ^ 62 →
    ∀ (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (MM : ModeMaps) (eb mode d c us so sn : Word) (xs : Array EIdx),
    CoreS dn s₀.mem a₀ vis fe MM eb → mode < 4 → eb = (mode >>> 1) &&& 1 → HW c → HW us →
    SpineR s₀.mem so sn xs → so.toNat + sn.toNat ≤ (spTop s₀.mem).toNat →
    CoreSpec p (n + 1) "iota_rec_c" [mode, vis, d, c, us, so, sn]
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size) decOptR s₀ a₀ dn vis fe MM eb ResW := by
  intro n hk F hnF hn62 s₀ a₀ dn vis fe MM eb mode d c us so sn xs hS hm4 hebm hcw hus hsa hsat
  refine triple_post (iotaRecC_spec p hp.recC n s₀ mode vis d c us so sn) fun r s' ⟨hloc, hW⟩ =>
    ⟨hloc, ?_⟩
  simp only [irCW] at hW
  have hspn := hS.spn
  have herec := hS.erec
  have hsz : xs.size = sn.toNat := hsa.size
  have hnone : ∀ (h0 : r.headD 0 = 0) (h1 : r.tail.headD 0 = 0) (hm : s'.mem = s₀.mem),
      (iotaRecCT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c) (decI us) xs
        xs.size).run a₀ = .ok (none, a₀) →
      CoreRef (iotaRecCT (decMode mode) (coreKnot (decMode mode) fe id F) fe d.toNat (decI c)
        (decI us) xs xs.size) a₀ decOptR dn s₀.mem vis fe MM eb r s'.mem ResW := by
    intro h0 h1 hm hrunT
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ hrunT
    refine ⟨hokF, ⟨MM, by rw [hstF, hm]; exact hS, KeptAll.refl _ _, by rw [hm]; exact StackKept.refl _⟩,
      ?_, ?_⟩
    · rw [hresF, decOptR_none_rec r h0]
    · unfold ResW HW; rw [h0, h1]; decide
  -- the recursor's record
  rcases c1 : callW p n "env_find" [c, vis] s₀.mem with _ | ⟨re, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hm1, hfnone, hfsome⟩ := irEnvFind p hp.toIotaProg' n dn s₀.mem vis fe hS.env c hcw re m1 c1
  subst m1
  by_cases f0 : re.headD 0 = 0
  · rw [if_pos f0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hnone h0.symm h1.symm hm.symm (cT_run_find _ _ _ _ _ _ _ _ a₀ (fun _ _ _ _ h => by
      rw [hfnone f0] at h; cases h))
  rw [if_neg f0] at hW
  obtain ⟨ci, hfind, hci⟩ := hfsome f0
  by_cases k5 : rdW (s₀.mem.arr64 EREC) (re.tail.headD 0) ≠ 5
  · rw [if_pos k5] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    have hnr := (decCI_rec_rd herec hci).2 k5
    exact hnone h0.symm h1.symm hm.symm (cT_run_find _ _ _ _ _ _ _ _ a₀ (fun cv mI rP rules h => by
      rw [hfind] at h; cases h; exact hnr cv mI rP rules rfl))
  rw [if_neg k5] at hW
  obtain ⟨cv, rules, rfl, hcv, hrules⟩ := (decCI_rec_rd herec hci).1 (Classical.not_not.mp k5)
  generalize hE0 : s₀.mem.arr64 EREC = E at *
  generalize hrecP : re.tail.headD 0 = recP at *
  -- the arity
  have hmIw := (rdW E (recP + 5)).toNat_lt
  by_cases s0 : sn = 0
  · rw [if_pos s0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hnone h0.symm h1.symm hm.symm (cT_run_arity _ _ _ _ _ _ _ _ a₀ _ _ _ _ hfind (by
      rw [hsz, s0]; simp))
  rw [if_neg s0] at hW
  have hsn1 : (sn - 1).toNat = sn.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by
      have : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
      rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
  have hsnp : sn.toNat ≠ 0 := fun h => s0 (UInt64.toNat_inj.mp (by simpa using h))
  by_cases a1 : sn - 1 ≠ rdW E (recP + 5)
  · rw [if_pos a1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hnone h0.symm h1.symm hm.symm (cT_run_arity _ _ _ _ _ _ _ _ a₀ _ _ _ _ hfind (by
      rw [hsz]; intro h; apply a1; apply UInt64.toNat_inj.mp; rw [hsn1]; omega))
  rw [if_neg a1] at hW
  have hn : xs.size = (rdW E (recP + 5)).toNat + 1 := by
    have := congrArg UInt64.toNat (Classical.not_not.mp a1); rw [hsn1] at this; omega
  -- the levels' length and the telescope
  simp only [irCTail] at hW
  obtain ⟨-, hname, hlps, hlen, htyw, htype⟩ := decCV_rd1 herec hcv
  rcases c2 : callW p n "ls_node" [us] s₀.mem with _ | ⟨rl, m2⟩ <;>
    simp only [c2, reduceCtorEq] at hW
  obtain ⟨t2, ht2, hs2, hne2, hr2⟩ := triple_of_callW (lsNode_spec p hp.lvl.lsnode n ⟨s₀.mem, Locals.init []⟩ us) c2
  have hm2 : m2 = s₀.mem := by rw [← ht2, hs2]
  subst hm2
  obtain ⟨o, l, hol⟩ : ∃ o l, rl = [o, l] := by
    rcases lsNodeW_cases s₀.mem us with h | ⟨o, l, h⟩
    · rw [hr2] at hne2; exact absurd h hne2
    · exact ⟨o, l, by rw [hr2]; exact h⟩
  have hvl := lsNodeW_viewLen hS.arena.1 hus (by rw [← hr2, hol])
  subst hol
  rw [hE0] at hW
  rcases c3 : callW p n "peel_pis" [sn, rdW E (recP + 4)] s₀.mem with _ | ⟨rp, m3⟩ <;>
    simp only [c3, reduceCtorEq] at hW
  obtain ⟨t3, ht3, hm3, -, -, hrunP⟩ := triple_of_callW
    (peelPis_refines' p hp.spine.peel n ⟨s₀.mem, Locals.init []⟩ a₀ hS.arena.1 sn _ htyw) c3
  have hm3' : s₀.mem = m3 := hm3.symm.trans ht3
  subst hm3'
  rw [hE0] at hW
  have hrunP' : (peelPis ((rdW E (recP + 5)).toNat + 1) cv.type).run a₀ =
      .ok (decOpt (rp.headD 0) (rp.tail.headD 0), a₀) := by
    rw [htype, ← hn, hsz]; exact hrunP
  have htk : (takeEidx xs xs.size).toList.length = (rdW E (recP + 5)).toNat + 1 := by
    rw [takeEidx_size]; simp [hn]
  by_cases u1 : [o, l].tail.headD 0 ≠ rdW E (recP + 3)
  · rw [if_pos u1] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hnone h0.symm h1.symm hm.symm (cT_run_check _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _ hfind hn hvl hrunP'
      (fun ⟨_, h2, _⟩ => u1 (by rw [hlen] at h2; exact UInt64.toNat_inj.mp h2)))
  rw [if_neg u1] at hW
  by_cases p0 : rp.headD 0 = 0
  · rw [if_pos p0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    exact hnone h0.symm h1.symm hm.symm (cT_run_check _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _ hfind hn hvl hrunP'
      (fun ⟨_, _, h3⟩ => by rw [p0] at h3; simp [decOpt] at h3))
  rw [if_neg p0] at hW
  -- the major
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  rcases c4 : callW p (N + 1) "iota_rec_major" [mode, vis, d, c, us, recP, so, sn] s₀.mem with _ | ⟨rr, m4⟩ <;>
    simp only [c4, reduceCtorEq] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨h0, h1, hm⟩ := hW
  have hma := iotaRecMajor_refines' p hp hc hw hsup hmtc hEI hER hEK N (hk.mono (by omega)) F
    (by omega) (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe MM eb mode d c us recP so sn cv rules xs hS
    hm4 hebm hcw hus
  simp only [hE0] at hma
  obtain ⟨hrun4, ⟨M4, hS4, hK4, hSt4⟩, hr4⟩ := CoreSpec.run (hma hcv hrules ⟨_, _, _, hfind⟩ hsa hsat
    (by omega)) c4
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ (cT_run_major _ _ _ _ _ _ _ _ a₀ _ _ _ _ _ _ _ _
    hfind hn hvl hrunP' ⟨htk, by
      rw [hlen]; have := Classical.not_not.mp u1; simp only [List.tail_cons, List.headD_cons] at this
      rw [this], by unfold decOpt; rw [if_neg p0]; rfl⟩ (by rw [takeEidx_size]; exact hrun4))
  refine ⟨hokF, ⟨M4, by rw [hstF, ← hm]; exact hS4, hK4, by rw [← hm]; exact hSt4⟩, ?_, ?_⟩
  · rw [hresF]; simp only [decOptR, h0, h1]
  · unfold ResW at hr4 ⊢; rw [← h0, ← h1]; exact hr4

/-! ## `iota_rec_at(mode, vis, d, hd, so, sn)` -/

/-- Model of `iota_rec_at`. -/
def irAtW (p : Prog) (n : Nat) (m : Mem) (mode vis d hd so sn : Word) : Option (Word × Word × Mem) :=
  match callW p n "iota_rec_head" [hd] m with
  | none => none
  | some (rv, m1) =>
  if rv.headD 0 = 0 then some (0, 0, m1) else
  match callW p n "iota_rec_c" [mode, vis, d, rv.tail.headD 0, rv.tail.tail.headD 0, so, sn] m1 with
  | none => none
  | some (rc, m2) => some (rc.headD 0, rc.tail.headD 0, m2)

theorem iotaRecAt_spec (p : Prog) (hp : p.lookup "iota_rec_at" = some iotaRecAtL) (n : Nat)
    (s₀ : St) (mode vis d hd so sn : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p (n + 1)) "iota_rec_at" [mode, vis, d, hd, so, sn]
    ⦃fun r s' => LocEq s' s₀ ∧ irAtW p n s₀.mem mode vis d hd so sn =
      some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, iotaRecAtL]
  vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
    callW_spec p n "iota_rec_head", callW_spec p n "iota_rec_c"] <;>
  simp_all [irAtW, BinOp.eval, Cmp.eval, LocEq, St.setLocs_cons, St.setLoc_loc, St.setLoc_mem,
    St.setLocs_nil, Locals.init_cons_zero, Locals.init_cons_succ, Sig.retVal, Sig.retOr]

section atRun
variable (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (hd : EIdx)
  (sargs : Array EIdx) (n : Nat)

theorem at_run_tag (a : AState) (ht : hd.tag ≠ ETag.const) :
    (iotaRecAt mode r fe depth hd sargs n).run a = .ok (none, a) := by
  have : (hd.tag == ETag.const) = false := by simpa using ht
  rw [iotaRecAt_eq]; simp only [this, Bool.false_eq_true, ↓reduceIte]; rfl

theorem at_run_c (a a' : AState) (c : NIdx) (us : LsIdx) (res : Option EIdx)
    (ht : hd.tag = ETag.const) (hv : a.store.viewConst hd = some (c, us))
    (h : (iotaRecCT mode r fe depth c us sargs n).run a = .ok (res, a')) :
    (iotaRecAt mode r fe depth hd sargs n).run a = .ok (res, a') := by
  have hvr : (viewConst hd).run a = .ok (some (c, us), a) := by
    show Except.ok (a.store.viewConst hd, a) = _; rw [hv]
  rw [iotaRecAt_eq]
  simp only [ht, beq_self_eq_true, ↓reduceIte, StateT.run_bind, hvr, except_ok_bind, h]

end atRun

/-- **`iota_rec_at` refines `iotaRecAt`** (`IotaRecAtOK`, what `whnf_app` assumes), from the
callees' specs and the stub assumption `ErecKeptRec` (the callees the pieces read the
record pool after leave it alone). -/
theorem iotaRecAt_refines' (p : Prog) (hp : IotaRecProg' p) (hc : IotaCallees p)
    (hw : WhnfCallees p) (hsup : ∀ fe : IFEnv, SupKeep fe) (hmtc : MajorToCtorOK p)
    (hEI : ErecKeptInst p) (hER : ErecKeptRec p) (hEK : ErecKeptKnot p)
    (n : Nat) (hk : KnotUpTo p n) : IotaRecAtOK p (n + 1) := by
  intro F s₀ a₀ dn vis fe M eb mode d hd so sn xs hnF hn62 hpre hhd hsa hsat
  have hS := hpre.rel
  refine triple_post (iotaRecAt_spec p hp.iotaRecAt n s₀ mode vis d hd so sn) fun r s' ⟨hloc, hW⟩
    => ⟨hloc, ?_⟩
  simp only [irAtW] at hW
  rcases c1 : callW p n "iota_rec_head" [hd] s₀.mem with _ | ⟨rv, m1⟩ <;>
    simp only [c1, reduceCtorEq] at hW
  obtain ⟨hm1, hnot, hyes⟩ := irCallW_head p hp.head n s₀.mem a₀ hS.arena.1 hd hhd rv m1 c1
  subst m1
  by_cases v0 : rv.headD 0 = 0
  · rw [if_pos v0] at hW
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨h0, h1, hm⟩ := hW
    obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ (at_run_tag (decMode mode)
      (coreKnot (decMode mode) fe id F) fe d.toNat (decE hd) xs xs.size a₀ (hnot v0))
    refine ⟨hokF, ⟨M, by rw [hstF, ← hm]; exact hS, KeptAll.refl _ _, by rw [← hm]; exact StackKept.refl _⟩,
      ?_, ?_⟩
    · rw [hresF, decOptR_none_rec r h0.symm]
    · unfold ResW HW; rw [← h0, ← h1]; decide
  rw [if_neg v0] at hW
  obtain ⟨htag, hview, hcw, husw⟩ := hyes v0
  have hvc := L.Ind.EStore.viewConst_of_view _ _ htag _ _ hview
  cases n with
  | zero => rw [callW_zero] at hW; cases hW
  | succ N =>
  rcases c2 : callW p (N + 1) "iota_rec_c" [mode, vis, d, rv.tail.headD 0, rv.tail.tail.headD 0, so, sn]
      s₀.mem with _ | ⟨rc, m2⟩ <;> simp only [c2, reduceCtorEq] at hW
  simp only [Option.some.injEq, Prod.mk.injEq] at hW
  obtain ⟨h0, h1, hm⟩ := hW
  obtain ⟨hrun2, ⟨M2, hS2, hK2, hSt2⟩, hr2⟩ := CoreSpec.run
    (iotaRecC_refines' p hp hc hw hsup hmtc hEI hER hEK N (hk.mono (by omega)) F
      (by omega) (by omega) ⟨s₀.mem, Locals.init []⟩ a₀ dn vis fe M eb mode d _ _ so sn xs hS
      hpre.mode4 hpre.eb_mode hcw husw hsa hsat) c2
  obtain ⟨hokF, hstF, hresF⟩ := AM.of_run_ok _ _ _ _ (at_run_c (decMode mode)
    (coreKnot (decMode mode) fe id F) fe d.toNat (decE hd) xs xs.size a₀ _ _ _ _ htag hvc hrun2)
  refine ⟨hokF, ⟨M2, by rw [hstF, ← hm]; exact hS2, hK2, by rw [← hm]; exact hSt2⟩, ?_, ?_⟩
  · rw [hresF]; simp only [decOptR, h0, h1]
  · unfold ResW at hr2 ⊢; rw [← h0, ← h1]; exact hr2

end L.Arena
