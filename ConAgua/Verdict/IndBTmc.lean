import ConAgua.Verdict.IndBTmm
import ConAgua.Verdict.IndBTmo
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# Error refinement of `target_major_of_const` (lane `verdicts-b`, helper `ib`)

Mirrors `tmcW_simC` (`IndT/RecGenTmf`): `block_shape_member_names` and `sl_find` are `closedNV`;
the member branch is `tmm_claim`, the outside branch `tmo_claim`.
-/

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep dMajor)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model tmcE_spec (p : Prog) (hf : p.lookup "target_major_of_const" = some targetMajorOfConst)
  fns [hf ↦ tmcE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 4000000 simp [Cmp.evalW, Cmp.eval] errors

section sims
variable {p : Prog} (hP : TmfProg p) (hIlpf : IlpfF p) (hcore : CoreStageClosed p)
  (hLC : LvlCacheProg p) (hnv : closedNV p _root_.L.Checker.nvFns = true) {env : ConLeche.Env}
  {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}

include hP hIlpf hcore hLC hnv in
theorem tmcE_claim (n : Nat) {m : Mem} {a : AState}
    {pp cao cal pfo pfl fvo fvl ao al x y : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe m a) (hq : DecB (fun m => decBS m pp.toNat) m bs) (hsrc : ShapeSrc m pp)
    (hcss : PSlR decCNS css cao cal m) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) m fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop m)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) m args) (hagb : ao.toNat + al.toNat ≤ iwTop m)
    (hx : H x) (hy : H y) (hPm : PosMR m)
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {IP : ConLeche.Name}
    (hIP : denoteN a.store.ns (decI x) = some IP) {usP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI y) = some usP) {argsP : List ConLeche.Expr}
    (hargsP : Frontend.denoteEList a.store args = some argsP) :
    ∀ e, tmcE p (n + 1) m vis pp cao cal pfo pfl fvo fvl ao al x y = .error e →
      ErrClaim (match bs.memberNames.findIdx? (· == (decI x : NIdx)) with
        | some t => tmoMemT bs css pfvs fvs args (decI x) (decI y) t
        | none => tmoOutT fe bs pfvs args (decI x) (decI y)) a e := by
  intro e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  obtain ⟨hqd, hq9, hptr⟩ := partsShapeFacts hq hsrc
  rw [tmcE.arm1] at he
  cases h4 : callE p n "block_shape_member_names" [pp] m with
  | error e4 =>
    rw [h4, tmcE.k_block_shape_member_names.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h4
  | ok q4 =>
  obtain ⟨r4, m4⟩ := q4
  obtain ⟨s4, hs4, hr4, hdn, hg4, hf4, ht4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_refines p hP.tmm.alloc hP.mnc hP.bsmn n _ pp bs hqd (by omega) hS.2.2.2.1 hS.2.2.2.2.2
      hsrc (fun o l j v h1 h2 h3 h4 => Nat.lt_of_succ_lt (hptr o l j v h1 h2 h3 h4))) (callW_of_callE h4)
  obtain ⟨s4', hs4', -, hW4⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (blockShapeMemberNames_spec p hP.tmm.alloc hP.mnc hP.bsmn n _ pp) (callW_of_callE h4)
  have hroom := memberNamesW_room hW4 hS.2.2.2.1
  rw [partsShapeK hqd hq9] at hroom
  have hkb : bs.k < 2 ^ 64 := by
    obtain ⟨o, l, -, hl', hg'⟩ := decAt_some (decBS_some hqd).1
    have := iwN_rdW hl' (by omega); rw [BlockShape.k, decPL_length _ hg']; exact this.2
  rw [UInt64.toNat_ofNat_of_lt' hkb] at hroom
  simp only at hr4 hdn hg4 hf4 ht4
  have hS4 : StageR dn vis fe s4.mem a := stage_frame_iw hS hf4 (by
    rw [← ht4]; simp only [iwTop] at hroom ⊢; omega)
  have hT4 : iwTop s4.mem < 2 ^ 64 := Nat.lt_of_le_of_lt hS4.2.1 hS4.2.2.2.1
  have hP4 : PosMR s4.mem := hPm.fr (MFr.of_iw hf4)
  have hA4 : AbsOK s4.mem := memberNamesW_afr (by rw [← hs4'.trans hs4.symm]; exact hW4) hA
  have hC4 : StageC dn vis fe env s4.mem a := hC.of_pstep hS4 hA4 (PStep.refl hC.check.state)
  subst hs4
  subst hr4
  rw [h4, tmcE.k_block_shape_member_names.arm1] at he
  simp only [List.headD_cons, List.tail_cons] at he
  obtain ⟨ws, hsl, hws, hwlt⟩ := slR_of_decHL s4.mem _ _ _ hdn (by omega)
  rw [UInt64.ofNat_toNat] at hsl
  cases h5 : callE p n "sl_find" [rdW (m.arr64 CTL) 200, UInt64.ofNat bs.k, x] s4.mem with
  | error e5 =>
    rw [h5, tmcE.k_sl_find.none] at he
    cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h5
  | ok q5 =>
  obtain ⟨r5, m5⟩ := q5
  obtain ⟨s5, hs5, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (slFind_spec p hP.find n _ _ _ x) (callW_of_callE h5)
  simp only at hm5
  have hlen : ws.length < 2 ^ 64 := by rw [slR_length hsl]; exact UInt64.toNat_lt _
  have hr5 := findW_ok n s4.mem _ _ x r5 ws hsl hW5 hlen
  have hm5' : m5 = s4.mem := hs5.symm.trans hm5
  subst hm5'
  rw [h5] at he
  rw [hws, findIdx_decIP ws x hwlt hx]
  have hT4' : (rdW (m.arr64 CTL) 200).toNat + bs.k = iwTop s4.mem := ht4
  cases hfi : ws.findIdx? (· == x) with
  | some i =>
    rw [hfi] at hr5
    subst hr5
    have hne : ([1, UInt64.ofNat i] : List Word).headD 0 ≠ 0 := by simp
    rw [tmcE.k_sl_find.arm1 p n vis pp cao cal pfo pfl fvo fvl ao al x y _ _ _ _ hne] at he
    obtain ⟨hi, -⟩ := List.findIdx?_eq_some_iff_getElem.mp hfi
    have hie : (UInt64.ofNat i : Word).toNat = i := UInt64.toNat_ofNat_of_lt' (show i < 2 ^ 64 by omega)
    simp only [List.tail_cons, List.headD_cons] at he
    cases h6 : callE p n "target_major_of_member" [pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y, UInt64.ofNat i]
        s4.mem with
    | error e6 =>
      rw [h6, tmcE.k_target_major_of_member.none] at he
      cases he
      have := CoreSpecE.of_callE (tmm_claim hP.tmm hnv n (s₀ := ⟨s4.mem, Locals.init []⟩) (a := a) (bs := bs)
        (css := css) (pfvs := pfvs) (fvs := fvs) (args := args) hS4 (hq.grow (decBS_mono _) hg4)
        (partsHsrc_grow hg4 hq9 hsrc) (hcss.grow decCNS_mono hg4) (hpf.grow (OMono.decHL _ _) hg4)
        (hfv.grow (OMono.decHL _ _) hg4) (Nat.le_trans hfvb hg4.1) (hag.grow (OMono.decHL _ _) hg4)
        (Nat.le_trans hagb hg4.1) hx hy hP4) h6
      rw [hie] at this
      exact this
    | ok q6 =>
      rw [h6] at he
      simp [tmcE.k_target_major_of_member] at he
  | none =>
    rw [hfi] at hr5
    subst hr5
    have hz : ([0, 0] : List Word).headD 0 = 0 := by simp
    rw [tmcE.k_sl_find.arm2 p n vis pp cao cal pfo pfl fvo fvl ao al x y _ _ _ _ hz] at he
    cases h6 : callE p n "target_major_of_outside" [vis, pp, pfo, pfl, x, y, ao, al, rdW (m.arr64 CTL) 200,
        UInt64.ofNat bs.k] s4.mem with
    | error e6 =>
      rw [h6, tmcE.k_target_major_of_member.none] at he
      cases he
      exact CoreSpecE.of_callE (tmo_claim hP.tmo hIlpf hcore hLC hnv n (s₀ := ⟨s4.mem, Locals.init []⟩) (a := a)
        (bs := bs) (pfvs := pfvs) (args := args) hS4 (hq.grow (decBS_mono _) hg4)
        (by show _ ≤ iwTop s4.mem; have := hg4.1; omega) hsl hwlt
        (fun j hj => by show _ < iwTop s4.mem; rw [UInt64.toNat_ofNat_of_lt' hkb] at hj; omega) hws.symm
        (hag.grow (OMono.decHL _ _) hg4) (Nat.le_trans hagb hg4.1) (hpf.grow (OMono.decHL _ _) hg4) hx hy hP4
        hC4 hA4 hshP hIP husP hargsP) h6
    | ok q6 =>
      rw [h6] at he
      simp [tmcE.k_target_major_of_member] at he

include hP hIlpf hcore hLC hnv in
/-- **`target_major_of_const`'s error claim** (every fuel). -/
theorem tmc_claim (N : Nat) {s₀ : St} {a : AState}
    {pp cao cal pfo pfl fvo fvl ao al x y : Word} {bs : BlockShape}
    {css : List (List (IConstantVal × Nat))} {pfvs fvs args : List EIdx}
    (hS : StageR dn vis fe s₀.mem a) (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcss : PSlR decCNS css cao cal s₀.mem) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs)
    (hfv : DecB (fun m => decHL m fvo.toNat fvl.toNat) s₀.mem fvs) (hfvb : fvo.toNat + fvl.toNat ≤ iwTop s₀.mem)
    (hag : DecB (fun m => decHL m ao.toNat al.toNat) s₀.mem args) (hagb : ao.toNat + al.toNat ≤ iwTop s₀.mem)
    (hx : H x) (hy : H y) (hPm : PosMR s₀.mem)
    (hC : StageC dn vis fe env s₀.mem a) (hA : AbsOK s₀.mem) {pP : ConLeche.BlockShape}
    (hshP : ConRon.Bridge.Inductives.dShape a.store bs = some pP) {IP : ConLeche.Name}
    (hIP : denoteN a.store.ns (decI x) = some IP) {usP : List ConLeche.Level}
    (husP : denoteLs a.store.lss (decI y) = some usP) {argsP : List ConLeche.Expr}
    (hargsP : Frontend.denoteEList a.store args = some argsP) :
    CoreSpecE p N "target_major_of_const" [vis, pp, cao, cal, pfo, pfl, fvo, fvl, ao, al, x, y]
      (match bs.memberNames.findIdx? (· == (decI x : NIdx)) with
        | some t => tmoMemT bs css pfvs fvs args (decI x) (decI y) t
        | none => tmoOutT fe bs pfvs args (decI x) (decI y)) s₀ a := by
  cases N with
  | zero => exact CoreSpecE.zero _ _ _ _ _ _
  | succ n =>
    refine CoreSpecE.of_runs fun e hc => ?_
    by_cases hk0 : e.cls = 0
    · exact ErrClaim.of_cls0 hk0
    exact tmcE_claim hP hIlpf hcore hLC hnv n hS hq hsrc hcss hpf hfv hfvb hag hagb hx hy hPm hC hA hshP hIP
      husP hargsP e
      (triple_of_callE_err (tmcE_spec p hP.tmc (n + 1) s₀ vis pp cao cal pfo pfl fvo fvl ao al x y) hc
        (Err.code_ne_of_cls hk0))

end sims

end L.Ind
