import ConAgua.Verdict.IndA4
import ConAgua.Verdict.IndBE
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen

/-!
# `check_block_idx_sorts`' error claim (lane `verdicts-b`, helper `ia2`, fork `blk`)

`check_block_idx_sorts_one` (`iisE_claim`: `check_struct_field_sorts_i`'s claim
`CheckStructFieldSortsIE`; the capacity aborts and `open_pis_at_fvars_f` claim nothing),
`check_block_idx_sorts` (`iisrE_claim` by induction on the fuel, the head's ok run by `iisW_simC`;
`checkBlockIdxSortsE_claim`: `CheckBlockIdxSortsE`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model iisrE_spec (p : Prog) (hf : p.lookup "check_block_idx_sorts" = some checkBlockIdxSorts)
  fns [hf ↦ iisrE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

l_model iisE_spec (p : Prog) (hf : p.lookup "check_block_idx_sorts_one" = some checkBlockIdxSortsOne)
  fns [hf ↦ iisE] grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] simp [rdW] errors

theorem blkE2_nv : ∀ f ∈ ["sl_cons", "rec2", "open_pis_at_fvars_f"], f ∈ _root_.L.Checker.nvFns := by
  decide +kernel

theorem iisE_k_opf_eq (p : Prog) (n : Nat) (vis nP ni srt : Word) (r : List Word) (m₁ : Mem)
    (h : r.headD 0 ≠ 0) :
    iisE.k_open_pis_at_fvars_f p n vis nP ni srt (.ok (r, m₁)) =
      iisE.j1 p n vis nP ni srt (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).1
        (idxTail nP (r.tail.headD 0) (r.tail.tail.headD 0)).2 m₁ := by
  unfold idxTail
  by_cases hl : nP < r.tail.tail.headD 0
  · rw [iisE.k_open_pis_at_fvars_f.arm1 _ _ _ _ _ _ _ _ h hl, ite_eq_left hl]
  · rw [iisE.k_open_pis_at_fvars_f.arm2 _ _ _ _ _ _ _ _ h hl, ite_eq_right hl]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (eSF : CheckStructFieldSortsIE p)

include hq henv hOpf hLC hLT hnv eSF in
/-- **`check_block_idx_sorts_one`'s error claim** (the model at fuel `n + 1`; `iisW_simC`'s
hypotheses). -/
theorem iisE_claim (hP : IdxProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp ms cv : Word} {bs : BlockShape} {msh : MemberShape} {cvv : IConstantVal}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hqd : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcv : DecB (fun m => decCVp m cv.toNat) m cvv)
    {bsP : ConLeche.BlockShape} {cvP : ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hw : ConLeche.Expr.WScoped 0 cvP.type)
    (_hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) (e : Err)
    (he : iisE p (n + 1) m vis pp ms cv = .error e) :
    ErrClaim (idxOneAM fe bs msh cvv) a e := by
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  have hS := hC.stage
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  obtain ⟨hnpw, hnpb, hrs32, hrse⟩ := partsShapeWords (IWGrow.refl m) hqd hq9
  have hmsT : decMS (truncM m) ms.toNat = some msh := hms
  obtain ⟨-, hni, -⟩ := decMS_some hmsT
  have hnilt := partsIwLt hni
  obtain ⟨hw1, hnib, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨htyl, htye⟩ := partsCVType hcv (w := cv) rfl
  obtain ⟨-, -, -, -, hsP, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hbsP
  by_cases hov : rdW (m.arr64 IW) (pp + 4) + rdW (m.arr64 IW) (ms + 1) < rdW (m.arr64 IW) (pp + 4)
  · rw [iisE.abort1 p n m vis pp ms cv hov] at he; cases he; exact absurd rfl hk0
  rw [iisE.arm1 p n m vis pp ms cv hov, hnpw, hw1] at he
  rw [hnpw, hw1] at hov
  have hk : (UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx : Word).toNat = bs.nP + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib]
  unfold idxOneAM
  cases h1 : callE p n "open_pis_at_fvars_f" [UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx,
      rdW (m.arr64 EREC) (cv + 3), 0] m with
  | error e1 =>
    rw [h1, iisE.k_open_pis_at_fvars_f.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (blkE2_nv _ (by simp)) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  have hsim := opfSimRA (n := n) (k := UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx) (i := 0) hOpf htyl hS hA
  rw [hk, htye] at hsim
  obtain ⟨x1, a1, hrun1, ⟨⟨hS1, hg1, hd1⟩, hr1⟩, hA1⟩ := hsim r1 m1 (callW_of_callE h1)
  refine ErrClaim.bind_right hrun1 ?_
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state
    (ConRon.Bridge.denoteCV_type hcvP) hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    rw [h1, iisE.k_open_pis_at_fvars_f.abort1 _ _ _ _ _ _ _ _ h0] at he; cases he; exact absurd rfl hk0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, htq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  rw [h1, iisE_k_opf_eq _ _ _ _ _ _ _ _ (by rw [h1']; decide), iisE.j1.arm1] at he
  show ErrClaim (checkStructFieldSortsI V fe true false bs.resSort bs.nP (fvs.drop bs.nP) [] msh.nIdx) a1 e
  obtain ⟨hdT, hbT⟩ := installIdxTail (k := UInt64.ofNat bs.nP) hfd hfb
  rw [UInt64.toNat_ofNat_of_lt' hnpb] at hdT
  have hxPos : ∀ (i : Nat), i < (UInt64.ofNat msh.nIdx : Word).toNat → ∀ (x : ConLeche.Expr),
      (xsP.drop bs.nP)[i]? = some x →
      ConLeche.Expr.WScoped ((UInt64.ofNat bs.nP : Word).toNat + i) x.fvarTypeD := by
    intro i _ x hx
    rw [List.getElem?_drop] at hx
    have := ConRon.Bridge.Inductives.openers_typeD_WScoped htq hw (bs.nP + i) x hx
    rw [UInt64.toNat_ofNat_of_lt' hnpb]
    simpa using this
  have hxsd := ConRon.Bridge.Inductives.denoteEList_drop hxs bs.nP
  cases h2 : callE p n "check_struct_field_sorts_i" [vis, 1, 0, rdW (m.arr64 IW) (pp + 6), UInt64.ofNat bs.nP,
      (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).1,
      (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).2, 0, 0,
      UInt64.ofNat msh.nIdx] m1 with
  | error e2 =>
    rw [h2, iisE.k_check_struct_field_sorts_i.none] at he; cases he
    have h := eSF hq henv hLC hLT hP.sum.hg hP.sum.hpw hP.sum.het hP.sum.hcn hP.sum.hfsb hP.sum.hcfg hP.sum.ha
      hP.sum.hcfs hP.sum.ad.ftd ⟨m1, Locals.init []⟩ a1 1 0 (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0
      (UInt64.ofNat msh.nIdx) (fvs.drop bs.nP) [] hC1 hA1 hdT hbT (by simp [decHL, hslice?]) (by simp) hrs32
      (by rw [hrse]; exact ConRon.Bridge.denoteL_ext hsP p1.ext)
      (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxsd hxPos n hn _ h2
    rw [hrse, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib,
      show ((1 : Word) != 0) = true from rfl, show ((0 : Word) != 0) = false from rfl] at h
    exact h
  | ok q2 =>
    obtain ⟨r2, m2⟩ := q2
    rw [h2, iisE.k_check_struct_field_sorts_i.arm1] at he
    cases h3 : callE p n "rec2" [r2.headD 0, r2.tail.headD 0] m2 with
    | error e3 =>
      rw [h3, iisE.k_rec2.none] at he; cases he
      exact ErrClaim.of_callE_nv hnv (blkE2_nv _ (by simp)) h3
    | ok q3 => obtain ⟨r3, m3⟩ := q3; rw [h3, iisE.k_rec2.arm1] at he; cases he

include hq henv hOpf hLC hLT hnv eSF in
/-- **`check_block_idx_sorts`' error claim** (the model at fuel `n`; `iisrW_simC`'s hypotheses). -/
theorem iisrE_claim (hP : IdxProg p) (pp : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
    (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (mo ml co cl : Word) (mss : List MemberShape) (cvs : List IConstantVal)
      (cvsP : List ConLeche.ConstantVal),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decMS mss mo ml m → PSlR decCVp cvs co cl m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    cvs.mapM (Frontend.denoteCV a.store) = some cvsP → (∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    ∀ e, iisrE p n m vis pp mo ml co cl = .error e →
      ErrClaim (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a e := by
  induction n with
  | zero =>
    intro m a mo ml co cl mss cvs cvsP _ _ _ _ _ _ _ _ _ _ e he
    rw [iisrE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a mo ml co cl mss cvs cvsP hC hA hqd hsrc hmss hcvs hbsP hcvsP hws hfe e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  by_cases hml : ml = 0
  · rw [iisrE.arm1 p n m vis pp mo ml co cl hml] at he; cases he
  by_cases hcl : cl = 0
  · rw [iisrE.arm2 p n m vis pp mo ml co cl hml hcl] at he; cases he
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvsP
  rw [iisrE.arm3 p n m vis pp mo ml co cl hml hcl, hw, hwc] at he
  rw [installIdx_cons]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  cases h1 : callE p n "check_block_idx_sorts_one" [vis, pp, UInt64.ofNat q, UInt64.ofNat c] m with
  | error e1 =>
    rw [h1, iisrE.k_check_block_idx_sorts_one.none] at he
    cases he
    have hW := triple_of_callE_err (iisE_spec p hP.one n ⟨m, Locals.init []⟩ vis pp
      (UInt64.ofNat q) (UInt64.ofNat c)) h1 (Err.code_ne_of_cls hk0)
    simp only at hW
    cases n with
    | zero => rw [iisE.eq_1] at hW; cases hW; exact absurd Err.cls_outOfFuel hk0
    | succ k =>
    exact ErrClaim.bind_left (iisE_claim hq henv hOpf hLC hLT hnv eSF hP k (by omega) hC hA hqd hsrc
      (by rw [hq']; exact hdm) (by rw [hc']; exact hdc) hbsP hcvP (hws _ List.mem_cons_self) hfe _ hW)
  | ok q1 =>
    obtain ⟨r1, m1⟩ := q1
    rw [h1, iisrE.k_check_block_idx_sorts_one.arm1] at he
    cases n with
    | zero => have := callW_of_callE h1; rw [callW_zero] at this; cases this
    | succ k =>
    obtain ⟨s', hs', -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (iis_spec p hP.one k _ vis pp _ _) (callW_of_callE h1)
    subst hs'
    obtain ⟨is, a1, hrun1, hC1, hg1, hd1, hA1, c1⟩ :=
      iisW_simC hq henv hOpf hLC hLT hP k (by omega) hC hA hqd hsrc (by rw [hq']; exact hdm)
        (by rw [hc']; exact hdc) hbsP hcvP (hws _ List.mem_cons_self) hfe r1 _ hW
    refine ErrClaim.bind_right hrun1 ?_
    obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
    cases h2 : iisrE p (k + 1) s'.mem vis pp (mo + 1) (ml - 1) (co + 1) (cl - 1) with
    | error e2 =>
      rw [h2, iisrE.k_check_block_idx_sorts.none] at he
      cases he
      exact ErrClaim.bind_left (ih (by omega) s'.mem a1 (mo + 1) (ml - 1) (co + 1) (cl - 1) rest cvs' cvsP' hC1 hA1
        (hqd.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) (hrest.grow decMS_mono hg1)
        (hcvs'.grow (fun q => OMono.decCVp q) hg1) (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hbsP)
        (ConRon.Bridge.Inductives.dExt_denoteCV.list c1.ext _ _ hcvsP')
        (fun cv h => hws cv (List.mem_cons_of_mem _ h)) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) _ h2)
    | ok q2 =>
      obtain ⟨r2, m2⟩ := q2
      rw [h2, iisrE.k_check_block_idx_sorts.arm1] at he
      cases h3 : callE p (k + 1) "sl_cons" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2 with
      | error e3 =>
        rw [h3, iisrE.k_sl_cons.none] at he; cases he
        exact ErrClaim.of_callE_nv hnv (blkE2_nv _ (by simp)) h3
      | ok q3 => obtain ⟨r3, m3⟩ := q3; rw [h3, iisrE.k_sl_cons.arm1] at he; cases he

end sims

/-- **`check_block_idx_sorts`' error claim** (`CheckBlockIdxSortsE`, the `err_stmt` of
`checkBlockIdxSorts_refinesC`), from `check_struct_field_sorts_i`'s. -/
theorem checkBlockIdxSortsE_claim {p : Prog} (hnv : closedNV p _root_.L.Checker.nvFns = true)
    (eSF : CheckStructFieldSortsIE p) : CheckBlockIdxSortsE p := by
  intro hq dn vis fe env henv hOpf hLC hLT hP s₀ a₀ pp mo ml co cl bs mss cvs hC hA hqd hsrc hmss hcvs
    bsP cvsP hbsP hcvsP hws hfe F hF e he
  by_cases hk0 : e.cls = 0
  · exact ErrClaim.of_cls0 hk0
  replace he := triple_of_callE_err (iisrE_spec p hP.idx F ⟨s₀.mem, Locals.init []⟩ vis pp mo ml co cl) he
    (Err.code_ne_of_cls hk0)
  simp only at he
  exact iisrE_claim hq henv hOpf hLC hLT hnv eSF hP pp bs F hF s₀.mem a₀ mo ml co cl mss cvs cvsP hC hA hqd hsrc
    hmss hcvs hbsP hcvsP hws hfe e he

end L.Ind
