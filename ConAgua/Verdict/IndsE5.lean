import ConAgua.Verdict.IndsE4
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.PartsPSlCons
/-!
# `check_block_agree`: one model and one refinement for both outcomes

`cbagE` (`l_model … unified`): member 0's telescope through its `Option` model, each member's
agreements through `cbaoE`. `cbag_ref` refines `checkBlockAgree` for both outcomes, by induction
on the fuel: member 0's unopened telescope is an internal abort, a member's agreements by
`cbao_ref`, the rest by induction. `checkBlockAgree_refinesC` is its ok half.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

set_option experimental.vcgen true

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`check_block_agree`'s model, both outcomes**: member 0's telescope through its `Option`
model, each member's agreements through `cbaoE`. -/
l_model cbagE_spec (p : Prog) (hf : p.lookup "check_block_agree" = some checkBlockAgree)
  (ho : p.lookup "check_block_agree_one" = some checkBlockAgreeOne)
  (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
  fns [hf ↦ cbagE]
  specs [callW_spec p n "open_pis_at_fvars_f", cbaoE_spec p ho hl n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)

include hq henv hOpf hLC in
/-- **`check_block_agree` refines `checkBlockAgree`**, both outcomes (member 0's telescope opened
per member, as the twin does; the denotations as con-ron's `checkBlockAgree_specF` asks). -/
theorem cbag_ref (hP : AgreeProg p) (nP c0 s0 : Word) (cv0 : IConstantVal) {cv0P : ConLeche.ConstantVal}
    {s0P : ConLeche.Level} (h0 : ConLeche.Expr.WScoped 0 cv0P.type) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (rest : List (IConstantVal × LIdx))
      (cvsP : List (ConLeche.ConstantVal × ConLeche.Level)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCVp m c0.toNat) m cv0 → H s0 →
    PSlR decTele rest o l m →
    Frontend.denoteCV a.store cv0 = some cv0P → denoteL a.store.ls (decI s0) = some s0P →
    rest.mapM (ConRon.Bridge.Inductives.BI.dCvL a.store) = some cvsP →
    (∀ x ∈ cvsP, ConLeche.Expr.WScoped 0 x.1.type) →
    RefE (VerdictCtx p) (cbagE p n m vis nP c0 s0 o l)
      (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a
      (fun v _ a' => AgreePost dn vis fe env m a v.2 a') := by
  induction n with
  | zero =>
    intro m a o l rest cvsP _ _ _ _ _ _ _ _ _
    rw [cbagE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a o l rest cvsP hC hA hc0 hs0 hrest hc0P hs0P hcvs hws
  have hS := hC.stage
  by_cases hl : l = 0
  · rw [cbagE.arm1 p n m vis nP c0 s0 o l hl]
    have : rest = [] := by
      have h := hrest.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact RefE.ret rfl ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, ⟨cvTa, sx⟩, rest', rfl, hw, hqb, hdx, hrest'⟩ := partsPSl_cons hrest hl
  obtain ⟨xP, restP, rfl, hx, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvs
  obtain ⟨hxcv, hxs⟩ := ConRon.Bridge.Inductives.BI.dCvL_inv hx
  dsimp only at hxcv hxs
  have hwx : ConLeche.Expr.WScoped 0 xP.1.type := hws _ List.mem_cons_self
  rw [cbagE.arm2 p n m vis nP c0 s0 o l hl]
  rw [installAgree_cons]
  obtain ⟨hty0, htye0⟩ := partsCVType hc0 (w := c0) rfl
  have hd0 : denoteE a.store (decI (rdW (m.arr64 EREC) (c0 + 3))) = some cv0P.type := by
    rw [htye0]; exact ConRon.Bridge.denoteCV_type hc0P
  -- member 0's telescope
  rcases h1 : callW p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (c0 + 3), 0] m with _ | ⟨r1, m1⟩
  · rw [liftE_none, cbagE.k_open_pis_at_fvars_f.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  by_cases hr0 : r1.headD 0 = 0
  · rw [cbagE.k_open_pis_at_fvars_f.abort1 p n vis nP c0 s0 o l r1 m1 hr0]
    exact RefE.of_cls0 rfl
  rw [cbagE.k_open_pis_at_fvars_f.arm1 p n vis nP c0 s0 o l r1 m1 hr0]
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1, hA1⟩ := opfF_okRA hty0 (callW_opfF hOpf h1) hS hA
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hd0 hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  rw [← htye0]
  cases x1 with
  | none => exact absurd hd1 hr0
  | some fb =>
  obtain ⟨fvs0, body0⟩ := fb
  obtain ⟨xs0, b0, hq0, hxs0, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  -- the twin's prefix: member 0's telescope opened
  have hpre : ∀ {β : Type} (k : List EIdx × EIdx → AM β),
      (openPisAtFvarsF nP.toNat (decI (rdW (m.arr64 EREC) (c0 + 3))) 0 >>= fun x =>
        unwrapOr x (.internal "block: type former telescope") >>= k).run a = (k (fvs0, body0)).run a1 := by
    intro β k
    simp only [StateT.run_bind]
    rw [show (0 : Nat) = UInt64.toNat 0 from rfl, hrun1]
    rfl
  refine RefE.of_run_eq (hpre _) ?_
  -- the member's record words, read in `m1`
  have hd1x : decTele (truncM m1) q = some (cvTa, sx) := hdx.grow (decTele_mono _) hg1
  simp only [decTele, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd1x
  obtain ⟨c, hc, cvv, hcv, sv, hsv, rfl, rfl⟩ := hd1x
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hol : o.toNat < iwTop m := by
    have := hrest.2
    have : 0 < l.toNat := by
      rcases Nat.eq_zero_or_pos l.toNat with h0 | h0
      · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) hl
      · exact h0
    omega
  have hw1 : rdW (m1.arr64 IW) o = UInt64.ofNat q := by
    rw [← hw]; simp only [rdW]; rw [hg1.iwGet _ hol]
  rw [hw1]
  obtain ⟨hwc, hcb, -⟩ := partsIwRd hc (w := UInt64.ofNat q) hq'
  obtain ⟨-, hsv'⟩ := rec2IwH_trunc hsv
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := UInt64.ofNat q) (k := 1) (by rw [hq']; exact hsv')
    hS1.iw.iwSize
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at hv
  rw [hwc, hv]
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hty := partsCVType hcv (w := UInt64.ofNat c) hc'
  rw [← hve]
  rw [← hve] at hxs
  have hxcv1 := ConRon.Bridge.denoteCV_ext hxcv p1.ext
  -- the member's agreements
  have hr2 := cbao_ref hq henv hOpf hLC hP n (by omega) (m := m1) (a := a1) (nP := nP)
    (fvs0O := r1.tail.headD 0) (fvs0L := r1.tail.tail.headD 0) (s0 := s0) (cvTa := UInt64.ofNat c) (s := v)
    hC1 hA1 hty hfd hfb hv32 hs0 (ConRon.Bridge.denoteCV_type hxcv1) hwx hxs0
    (ConRon.Bridge.Inductives.openers_typeD_WScoped hq0 h0)
    (ConRon.Bridge.denoteL_ext hxs p1.ext) (ConRon.Bridge.denoteL_ext hs0P p1.ext)
  rcases h2 : cbaoE p n m1 vis nP (r1.tail.headD 0) (r1.tail.tail.headD 0) s0 (UInt64.ofNat c) v
    with e2 | ⟨r2, m2⟩
  · rw [h2] at hr2
    rw [cbagE.k_check_block_agree_one.none]
    exact RefE.bind_left hr2
  rw [h2] at hr2
  obtain ⟨_, a2, hrun2, ⟨hC2, hg2, hA2, c2⟩⟩ := hr2
  rw [cbagE.k_check_block_agree_one.arm1]
  refine RefE.bind_right hrun2 ?_
  have c02 := (p1.toCore hC.check).trans c2
  have ih' := ih (by omega) m2 a2 (o + 1) (l - 1) rest' restP hC2 hA2
    (hc0.grow (OMono.decCVp _) (hg1.trans hg2))
    hs0 (hrest'.grow decTele_mono (hg1.trans hg2)) (ConRon.Bridge.denoteCV_ext hc0P c02.ext)
    (ConRon.Bridge.denoteL_ext hs0P c02.ext)
    (ConRon.Bridge.Inductives.BI.dCvL_ext.list c02.ext _ _ hrestP)
    (fun y hy => hws y (List.mem_cons_of_mem _ hy))
  rcases h3 : cbagE p n m2 vis nP c0 s0 (o + 1) (l - 1) with e3 | ⟨r3, m3⟩
  · rw [h3] at ih'
    rw [cbagE.k_check_block_agree.none]
    exact ih'
  rw [h3] at ih'
  obtain ⟨_, a3, hrun3, ⟨hC3, hg3, hA3, c3⟩⟩ := ih'
  rw [cbagE.k_check_block_agree.arm1]
  exact RefE.ret hrun3 ⟨hC3, (hg1.trans hg2).trans hg3, hA3, c02.trans c3⟩

include hq henv hOpf hLC in
/-- **`check_block_agree` refines `checkBlockAgree`** under `StageC` (the knot's
`is_def_eq_core`; the denotations as con-ron's `checkBlockAgree_specF` asks): member 0's constant
decoded below the tops, its sort a handle, the other members a slice of checked formers. -/
@[refines ConRon.Arena.checkBlockAgree]
theorem checkBlockAgree_refinesC (hP : AgreeProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP c0 s0 o l : Word)
    (cv0 : IConstantVal) (rest : List (IConstantVal × LIdx)) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem) (hc0 : DecB (fun m => decCVp m c0.toNat) s₀.mem cv0) (hs0 : H s0)
    (hrest : PSlR decTele rest o l s₀.mem) {cv0P : ConLeche.ConstantVal} {s0P : ConLeche.Level}
    {cvsP : List (ConLeche.ConstantVal × ConLeche.Level)}
    (hc0P : Frontend.denoteCV a₀.store cv0 = some cv0P) (h0 : ConLeche.Expr.WScoped 0 cv0P.type)
    (hs0P : denoteL a₀.store.ls (decI s0) = some s0P)
    (hcvs : rest.mapM (ConRon.Bridge.Inductives.BI.dCvL a₀.store) = some cvsP)
    (hws : ∀ x ∈ cvsP, ConLeche.Expr.WScoped 0 x.1.type) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_agree" [vis, nP, c0, s0, o, l]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a₀ ∧
      StageC dn vis fe env s'.mem
        (AM.st (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (RefE.triple (cbagE_spec p hP.agree hP.one hP.lvl n s₀ vis nP c0 s0 o l)
    (cbag_ref hq henv hOpf hLC hP nP c0 s0 cv0 h0 n hn _ a₀ o l rest cvsP hC hA hc0 hs0 hrest hc0P hs0P hcvs hws))
    fun _ _ ⟨hl, _, _, hrun, hR⟩ =>
      let ⟨hok, hst, _⟩ := AM.of_run_ok _ _ _ _ hrun
      ⟨hl, hok, hst ▸ hR.stage, hR.grow, hR.abs⟩

end sims

end L.Ind
