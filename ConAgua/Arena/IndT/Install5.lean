import ConAgua.Arena.IndT.Sum3
import ConAgua.Arena.IndInstallSpec.IcvgW
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl

/-!
# `checkBlockIdxSorts` under `StageC` (lane `indstaget`)

`check_block_idx_sorts`' model, from `StageC` and con-ron's preconditions of
`checkBlockIdxSorts_specF` (the shape, the members and the formers denote, every stored former
closed, the environment denotes), its twin side transcribed from that spec's proof: the former's
opened telescope (`openPisAtFvarsF_run`), the index binders' sorts (`fsortsW_okC`, con-ron's
`checkStructFieldSortsI_spec` on its run for the `CoreStep`), the records and conses (L only).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

theorem installCons_afr {p : Prog} (hP : CstProg p) {n : Nat} {x o l : Word} {r : List Word}
    {m m' : Mem} (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) : AFr m m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ x o l) h
  exact consW_afr hW

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop)

include hq henv hLC hLT in
/-- `check_struct_field_sorts_i` under `StageC` as a `Sim` of its call. -/
theorem installSimFsortsC (hP : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    (isP large s nP fo fl io il j : Word) (hs : H s) (fvs idx : List EIdx) {sP : ConLeche.Level}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hsP : denoteL a.store.ls (decI s) = some sP)
    (hfd : decHL m fo.toNat fl.toNat = some fvs) (hfb : fo.toNat + fl.toNat ≤ iwTop m)
    (hid : decHL m io.toNat il.toNat = some idx) (hib : io.toNat + il.toNat ≤ iwTop m)
    (hnj : nP.toNat + j.toNat < 2 ^ 64) {fvsP : List ConLeche.Expr}
    (hfP : Frontend.denoteEList a.store fvs = some fvsP)
    (hws : ∀ i, i < j.toNat → ∀ x, fvsP[i]? = some x →
      ConLeche.Expr.WScoped (nP.toNat + i) x.fvarTypeD) :
    Sim (callW p n "check_struct_field_sorts_i" [vis, isP, large, s, nP, fo, fl, io, il, j] m)
      (checkStructFieldSortsI V fe (isP != 0) (large != 0) (decI s) nP.toNat fvs idx j.toNat) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        decHL m' (r.headD 0).toNat (r.tail.headD 0).toNat = some x ∧
        (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m' ∧ AbsOK m') := by
  rcases n with _ | k
  · intro r m' e; rw [callW_zero] at e; cases e
  intro r m' e
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (fsortsW_spec p hP.hg hP.hpw hP.het hP.hcn hP.hfsb hP.hcfg hP.ha hP.hcfs hP.ad.ftd (realCall p)
      (realCall_spec p) k _ vis isP large s nP fo fl io il j) e
  exact fsortsW_okC hq henv hLC hLT k (by omega) m a isP large s nP fo fl io il j fvs idx hC hA hfd hfb hid
    hib hs hsP hnj hfP hws r s'.mem hW

include hq henv hOpf hLC hLT in
/-- **`check_block_idx_sorts_one` under `StageC`** (twin side: one member of con-ron's
`checkBlockIdxSorts_specF`'s proof). -/
theorem iisW_simC (hP : IdxProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {pp ms cv : Word} {bs : BlockShape} {msh : MemberShape} {cvv : IConstantVal}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hqd : DecB (fun m => decBS m pp.toNat) m bs)
    (hsrc : ShapeSrc m pp)
    (hms : DecB (fun m => decMS m ms.toNat) m msh) (hcv : DecB (fun m => decCVp m cv.toNat) m cvv)
    {bsP : ConLeche.BlockShape} {cvP : ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hcvP : Frontend.denoteCV a.store cvv = some cvP) (hw : ConLeche.Expr.WScoped 0 cvP.type)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (iisW p n m vis pp ms cv) (idxOneAM fe bs msh cvv) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decIS m (r.headD 0).toNat) m' x ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
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
  unfold iisW
  rw [hnpw, hw1]
  split
  · exact Sim.of_none
  rename_i hov
  have hk : (UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx : Word).toNat = bs.nP + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib]
  unfold idxOneAM
  refine Sim.bindK (K := iisK1 p n vis (UInt64.ofNat bs.nP) (UInt64.ofNat msh.nIdx) (rdW (m.arr64 IW) (pp + 6)))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none else iisK2 p n (callW p n "check_struct_field_sorts_i"
      [vis, 1, 0, rdW (m.arr64 IW) (pp + 6), UInt64.ofNat bs.nP,
        (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).1,
        (idxTail (UInt64.ofNat bs.nP) (r1.tail.headD 0) (r1.tail.tail.headD 0)).2, 0, 0,
        UInt64.ofNat msh.nIdx] m1)) (by simp [iisK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iisK1_none p n m₁ _ _ _ _ r h, ite_eq_left h]
      · rw [iisK1_some p n m₁ _ _ _ _ r h, ite_eq_right h])
    (by
      have h := opfSimRA (n := n) (k := UInt64.ofNat bs.nP + UInt64.ofNat msh.nIdx) (i := 0) hOpf htyl hS hA
      rw [hk, htye] at h
      exact h) ?_
  rintro r1 x1 m1 a1 ⟨⟨⟨hS1, hg1, hd1⟩, hr1⟩, hA1⟩
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state
    (ConRon.Bridge.denoteCV_type hcvP) hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, ite_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, htq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, ite_false]
  show Sim _ (checkStructFieldSortsI V fe true false bs.resSort bs.nP (fvs.drop bs.nP) [] msh.nIdx) a1 _
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
  refine Sim.tail (K := iisK2 p n) (body := fun r2 m2 => iisK3 (callW p n "rec2"
      [r2.headD 0, r2.tail.headD 0] m2)) rfl (fun _ _ => rfl)
    (by
      have h := installSimFsortsC (dn := dn) (fe := fe) hq henv hLC hLT hP.sum n hn 1 0
        (rdW (m.arr64 IW) (pp + 6)) (UInt64.ofNat bs.nP) _ _ 0 0 (UInt64.ofNat msh.nIdx) hrs32
        (fvs.drop bs.nP) [] hC1 hA1 (by rw [hrse]; exact ConRon.Bridge.denoteL_ext hsP p1.ext) hdT hbT (by simp [decHL, hslice?]) (by simp)
        (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxsd hxPos
      rw [hrse, UInt64.toNat_ofNat_of_lt' hnpb, UInt64.toNat_ofNat_of_lt' hnib,
        show ((1 : Word) != 0) = true from rfl, show ((0 : Word) != 0) = false from rfl] at h
      exact Sim.withRunC h) ?_
  rintro r2 isorts m2 a2 ⟨⟨hC2, hg2, hdl, hbl, hA2⟩, hr2⟩ r' m' e
  obtain ⟨c2, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv true false bs.resSort bsP.resSort bs.nP (fvs.drop bs.nP) []
    (xsP.drop bs.nP) [] msh.nIdx (fun i hi x hx => by
      have := hxPos i (by rw [UInt64.toNat_ofNat_of_lt' hnib]; exact hi) x hx
      rwa [UInt64.toNat_ofNat_of_lt' hnpb] at this) a1 a2 isorts hC1.check
    ⟨ConRon.Bridge.denoteL_ext hsP p1.ext, hxsd, rfl, ConRon.Bridge.denoteFEnv_mono p1.ext hfe⟩ hr2
  obtain ⟨⟨r3, m3⟩, h3, e⟩ := of_K e rfl; rw [iisK3_some] at e
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj e)
  obtain ⟨s3, rfl, -, hW3⟩ := triple_of_callW (s₀ := ⟨m2, Locals.init []⟩)
    (rec2_specW p hP.alloc n hP.rec2 _ _ _) h3
  obtain ⟨hS3, hg3, hr3, hget, htop⟩ := recW_stage hW3 hC2.stage rfl
  have hA3 := recW_afr hW3 hA2
  subst hr3
  refine ⟨hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state), (hg1.trans hg2).trans hg3, ?_, hA3,
    (p1.toCore hC.check).trans c2⟩
  simp only [List.headD_cons]
  have e0 : r2.getD 0 0 = r2.headD 0 := by rcases r2 with _ | ⟨_, _⟩ <;> rfl
  have e1 : r2.getD 1 0 = r2.tail.headD 0 := by rcases r2 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have hq0 : (rdW (m2.arr64 CTL) 200).toNat < iwTop s3.mem := by rw [htop]; simp [iwTop]
  have hq1 : (rdW (m2.arr64 CTL) 200).toNat + 1 < iwTop s3.mem := by rw [htop]; simp [iwTop]
  show decIS (truncM s3.mem) _ = some isorts
  have w0 : iwN (truncM s3.mem) (rdW (m2.arr64 CTL) 200).toNat = some (r2.headD 0).toNat := by
    rw [iwN_truncM hq0]; have := hget 0 (by simp); simp only [Nat.add_zero] at this
    simp [iwN, nat?, iwA, this]
  have w1 : iwN (truncM s3.mem) ((rdW (m2.arr64 CTL) 200).toNat + 1) = some (r2.tail.headD 0).toNat := by
    rw [iwN_truncM hq1]; have := hget 1 (by simp)
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at this
    simp [iwN, nat?, iwA, this]
  have hdB := (decHL_decB hdl hbl).grow (OMono.decHL _ _) hg3
  simp only [decIS, decAt, w0, w1, Option.bind_eq_bind, Option.bind_some]
  exact hdB

include hq henv hOpf hLC hLT in
/-- **`check_block_idx_sorts` under `StageC`** (twin side: con-ron's `checkBlockIdxSorts_specF`'s
proof). -/
theorem iisrW_simC (hP : IdxProg p) (pp : Word) (bs : BlockShape) {bsP : ConLeche.BlockShape}
    (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (mo ml co cl : Word) (mss : List MemberShape) (cvs : List IConstantVal)
      (cvsP : List ConLeche.ConstantVal),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decMS mss mo ml m → PSlR decCVp cvs co cl m →
    ConRon.Bridge.Inductives.dShape a.store bs = some bsP →
    cvs.mapM (Frontend.denoteCV a.store) = some cvsP → (∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    Sim (iisrW p n m vis pp mo ml co cl) (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        PSlR decIS x (r.headD 0) (r.tail.headD 0) m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  induction n with
  | zero => intros; rw [iisrW.eq_1]; exact Sim.of_none
  | succ n ih =>
  intro m a mo ml co cl mss cvs cvsP hC hA hqd hsrc hmss hcvs hbsP hcvsP hws hfe
  by_cases hml : ml = 0
  · rw [iisrW.arm1 p n m vis pp mo ml co cl hml]
    have : mss = [] := by
      have h := hmss.1; simp only [DecB, hml] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hC, IWGrow.refl m, PSlR.nil decIS m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hcl : cl = 0
  · rw [iisrW.arm2 p n m vis pp mo ml co cl hml hcl]
    have : cvs = [] := by
      have h := hcvs.1; simp only [DecB, hcl] at h
      simpa [decPL] using h.symm
    subst this
    have : ConRon.Arena.checkBlockIdxSorts V fe bs mss [] = pure [] := by
      cases mss <;> simp [ConRon.Arena.checkBlockIdxSorts]
    rw [this]
    exact Sim.ret ⟨hC, IWGrow.refl m, PSlR.nil decIS m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, msh, rest, rfl, hw, hqb, hdm, hrest⟩ := partsPSl_cons hmss hml
  obtain ⟨c, cvv, cvs', rfl, hwc, hcb, hdc, hcvs'⟩ := partsPSl_cons hcvs hcl
  obtain ⟨cvP, cvsP', rfl, hcvP, hcvsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvsP
  rw [iisrW.arm3 p n m vis pp mo ml co cl hml hcl, hw, hwc, installIdx_cons]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  rcases n with _ | k
  · rw [callW_zero]; rw [iisrW.k_check_block_idx_sorts_one.none]; exact Sim.of_none
  refine Sim.bindK (K := iisrW.k_check_block_idx_sorts_one p (k + 1) vis pp mo ml co cl) (body := fun r1 m1 => iisrW.k_check_block_idx_sorts p (k + 1) (r1.headD 0)
      (iisrW p (k + 1) m1 vis pp (mo + 1) (ml - 1) (co + 1) (cl - 1))) (iisrW.k_check_block_idx_sorts_one.none ..)
      (fun r m₁ => iisrW.k_check_block_idx_sorts_one.arm1 p (k + 1) vis pp mo ml co cl r m₁)
    (Q := fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        DecB (fun m => decIS m (r.headD 0).toNat) m' x ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a')
    (fun r m' e => by
      obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (iis_spec p hP.one k _ vis pp _ _) e
      exact iisW_simC hq henv hOpf hLC hLT hP k (by omega) hC hA hqd hsrc (by rw [hq']; exact hdm) (by rw [hc']; exact hdc)
        hbsP hcvP (hws _ List.mem_cons_self) hfe r s'.mem hW) ?_
  rintro r1 is m1 a1 ⟨hC1, hg1, hd1, hA1, c1⟩
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hqd hsrc
  refine Sim.bindK (K := iisrW.k_check_block_idx_sorts p (k + 1) (r1.headD 0)) (body := fun r2 m2 => iisrW.k_sl_cons p (callW p (k + 1) "sl_cons"
      [r1.headD 0, r2.headD 0, r2.tail.headD 0] m2)) (iisrW.k_check_block_idx_sorts.none ..)
      (fun r m₁ => iisrW.k_check_block_idx_sorts.arm1 p (k + 1) (r1.headD 0) r m₁)
    (ih (by omega) m1 a1 (mo + 1) (ml - 1) (co + 1) (cl - 1) rest cvs' cvsP' hC1 hA1
      (hqd.grow (decBS_mono _) hg1) (partsHsrc_grow hg1 hq9 hsrc) (hrest.grow decMS_mono hg1)
      (hcvs'.grow (fun q => OMono.decCVp q) hg1) (ConRon.Bridge.Inductives.dShape_ext c1.ext _ _ hbsP)
      (ConRon.Bridge.Inductives.dExt_denoteCV.list c1.ext _ _ hcvsP')
      (fun cv h => hws cv (List.mem_cons_of_mem _ h)) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe)) ?_
  rintro r2 rs m2 a2 ⟨hC2, hg2, hd2, hA2, c2⟩
  refine Sim.mstep (K := iisrW.k_sl_cons p) rfl (fun _ _ => rfl) fun r3 m3 h3 => ?_
  obtain ⟨hS3, hg3, hd3⟩ := installConsRun hP.toCstProg decIS_mono h3 hC2.stage hd2
    (hd1.grow (decIS_mono _) hg2)
  have hA3 := installCons_afr hP.toCstProg h3 hA2
  exact Sim.ret ⟨hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state), (hg1.trans hg2).trans hg3,
    by simpa using hd3, hA3, c1.trans c2⟩

include hq henv hOpf hLC hLT in
/-- **`check_block_idx_sorts` refines `checkBlockIdxSorts`** under `StageC` (the knot's core
calls; the denotations as con-ron's `checkBlockIdxSorts_specF` asks): every member's index sorts a
slice of `[off, len]` pointers below the tops. -/
@[refines ConRon.Arena.checkBlockIdxSorts]
theorem checkBlockIdxSorts_refinesC (hP : IdxProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (pp mo ml co cl : Word)
    (bs : BlockShape) (mss : List MemberShape) (cvs : List IConstantVal)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hqd : DecB (fun m => decBS m pp.toNat) s₀.mem bs)
    (hsrc : ShapeSrc s₀.mem pp) (hmss : PSlR decMS mss mo ml s₀.mem) (hcvs : PSlR decCVp cvs co cl s₀.mem)
    {bsP : ConLeche.BlockShape} {cvsP : List ConLeche.ConstantVal}
    (hbsP : ConRon.Bridge.Inductives.dShape a₀.store bs = some bsP)
    (hcvsP : cvs.mapM (Frontend.denoteCV a₀.store) = some cvsP)
    (hws : ∀ cv ∈ cvsP, ConLeche.Expr.WScoped 0 cv.type)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_idx_sorts" [vis, pp, mo, ml, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decIS (AM.res (ConRon.Arena.checkBlockIdxSorts V fe bs mss cvs) a₀) (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (iisr_spec p hP.idx n s₀ vis pp mo ml co cl) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hC', hg, hd, hA', _⟩ := Sim.run (iisrW_simC hq henv hOpf hLC hLT hP pp bs n hn _ a₀ mo ml co cl mss cvs cvsP
      hC hA hqd hsrc hmss hcvs hbsP hcvsP hws hfe) hm
    ⟨hl, hok, hC', hg, hd, hA'⟩

end sims

end L.Ind
