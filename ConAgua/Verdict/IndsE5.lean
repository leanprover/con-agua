import ConAgua.Verdict.IndsE4

/-!
# `check_block_agree`'s error refinement (lane `verdicts-b`, helper `ia2-inds`)

`iagW_simC`'s proof on the error model `cbagE`, by induction on the fuel: member 0's unopened
telescope is an internal abort, a member's agreement by `cbaoE_claim`, the rest by induction.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)


namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hnv : closedNV p _root_.L.Checker.nvFns = true) (hcE : CoreStubsE p)

include hq henv hOpf hLC hnv hcE in
/-- **`check_block_agree`'s error claim** (the model at L fuel `n`, `iagW_simC`'s hypotheses). -/
theorem cbagE_claim (hP : AgreeProg p) (nP c0 s0 : Word) (cv0 : IConstantVal) {cv0P : ConLeche.ConstantVal}
    {s0P : ConLeche.Level} (h0 : ConLeche.Expr.WScoped 0 cv0P.type) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (rest : List (IConstantVal × LIdx))
      (cvsP : List (ConLeche.ConstantVal × ConLeche.Level)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCVp m c0.toNat) m cv0 → H s0 →
    PSlR decTele rest o l m →
    Frontend.denoteCV a.store cv0 = some cv0P → denoteL a.store.ls (decI s0) = some s0P →
    rest.mapM (ConRon.Bridge.Inductives.BI.dCvL a.store) = some cvsP →
    (∀ x ∈ cvsP, ConLeche.Expr.WScoped 0 x.1.type) →
    ∀ e, cbagE p n m vis nP c0 s0 o l = .error e →
      ErrClaim (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a e := by
  induction n with
  | zero =>
    intro m a o l rest cvsP _ _ _ _ _ _ _ _ _ e he
    rw [cbagE.eq_1] at he; cases he; exact ErrClaim.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a o l rest cvsP hC hA hc0 hs0 hrest hc0P hs0P hcvs hws e he
  have hS := hC.stage
  by_cases hl : l = 0
  · rw [cbagE.arm1 p n m vis nP c0 s0 o l hl] at he; cases he
  obtain ⟨q, ⟨cvTa, sx⟩, rest', rfl, hw, hqb, hdx, hrest'⟩ := partsPSl_cons hrest hl
  obtain ⟨xP, restP, rfl, hx, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvs
  obtain ⟨hxcv, hxs⟩ := ConRon.Bridge.Inductives.BI.dCvL_inv hx
  dsimp only at hxcv hxs
  have hwx : ConLeche.Expr.WScoped 0 xP.1.type := hws _ List.mem_cons_self
  rw [cbagE.arm2 p n m vis nP c0 s0 o l hl] at he
  rw [installAgree_cons]
  obtain ⟨hty0, htye0⟩ := partsCVType hc0 (w := c0) rfl
  have hd0 : denoteE a.store (decI (rdW (m.arr64 EREC) (c0 + 3))) = some cv0P.type := by
    rw [htye0]; exact ConRon.Bridge.denoteCV_type hc0P
  cases h1 : callE p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (c0 + 3), 0] m with
  | error e1 =>
    rw [h1, cbagE.k_open_pis_at_fvars_f.none] at he; cases he
    exact ErrClaim.of_callE_nv hnv (by decide +kernel) h1
  | ok q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [h1] at he
  by_cases hr0 : r1.headD 0 = 0
  · rw [cbagE.k_open_pis_at_fvars_f.abort1 p n vis nP c0 s0 o l r1 m1 hr0] at he; cases he
    exact ErrClaim.of_cls0 rfl
  rw [cbagE.k_open_pis_at_fvars_f.arm1 p n vis nP c0 s0 o l r1 m1 hr0] at he
  obtain ⟨x1, a1, hrun1, hS1, hg1, hd1, hA1⟩ := opfF_okRA hty0 (callW_opfF hOpf (callW_of_callE h1)) hS hA
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
    rw [← hw]; simp only [rdW]; rw [hg1.2.2.1 _ hol]
  rw [hw1] at he
  obtain ⟨hwc, hcb, -⟩ := partsIwRd hc (w := UInt64.ofNat q) hq'
  obtain ⟨-, hsv'⟩ := rec2IwH_trunc hsv
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := UInt64.ofNat q) (k := 1) (by rw [hq']; exact hsv')
    hS1.2.2.2.1
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at hv
  rw [hwc, hv] at he
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hty := partsCVType hcv (w := UInt64.ofNat c) hc'
  rw [← hve]
  rw [← hve] at hxs
  have hxcv1 := ConRon.Bridge.denoteCV_ext hxcv p1.ext
  cases h2 : callE p n "check_block_agree_one" [vis, nP, r1.tail.headD 0, r1.tail.tail.headD 0, s0,
      UInt64.ofNat c, v] m1 with
  | error e2 =>
    rw [h2, cbagE.k_check_block_agree_one.none] at he; cases he
    have hcl := cbaoE_claim hnv hcE hq henv hOpf hLC hP.doms hP.lvl hP.one hP.ad ⟨m1, Locals.init []⟩ a1 nP _ _ s0 _ v
      cvv fvs0 hC1 hA1 hty hfd hfb hv32 hs0
      (ConRon.Bridge.denoteCV_type hxcv1) hwx hxs0
      (ConRon.Bridge.Inductives.openers_typeD_WScoped hq0 h0)
      (ConRon.Bridge.denoteL_ext hxs p1.ext) (ConRon.Bridge.denoteL_ext hs0P p1.ext) n (by omega) e h2
    exact ErrClaim.of_twin (ErrClaim.bind_left hcl) fun ce hce => by rw [hpre]; exact hce
  | ok q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [h2, cbagE.k_check_block_agree_one.arm1] at he
  cases n with
  | zero => have := callW_of_callE h2; rw [callW_zero] at this; cases this
  | succ k =>
  obtain ⟨s2, hs2, -, hok, hC2, hg2, hA2, c2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (checkBlockAgreeOne_refinesC hq henv hOpf hLC hP.doms hP.lvl hP.one hP.ad k (by omega)
      ⟨m1, Locals.init []⟩ a1 nP _ _ s0 _ v cvv fvs0 hC1 hA1 hty hfd hfb hv32 hs0
      (ConRon.Bridge.denoteCV_type hxcv1) hwx hxs0
      (ConRon.Bridge.Inductives.openers_typeD_WScoped hq0 h0)
      (ConRon.Bridge.denoteL_ext hxs p1.ext) (ConRon.Bridge.denoteL_ext hs0P p1.ext)) (callW_of_callE h2)
  subst hs2
  have hrun2 := partsRunOfOk hok
  generalize AM.st (agreeBodyAM fe nP.toNat fvs0 cvv (decI v) (decI s0)) a1 = a2 at hrun2 hC2 c2
  have c02 := (p1.toCore hC.check).trans c2
  cases h3 : cbagE p (k + 1) s2.mem vis nP c0 s0 (o + 1) (l - 1) with
  | error e3 =>
    rw [h3, cbagE.k_check_block_agree.none] at he; cases he
    have hcl := ih (by omega) s2.mem a2 (o + 1) (l - 1) rest' restP hC2 hA2
      (hc0.grow (OMono.decCVp _) (hg1.trans hg2))
      hs0 (hrest'.grow decTele_mono (hg1.trans hg2)) (ConRon.Bridge.denoteCV_ext hc0P c02.ext)
      (ConRon.Bridge.denoteL_ext hs0P c02.ext)
      (ConRon.Bridge.Inductives.BI.dCvL_ext.list c02.ext _ _ hrestP)
      (fun y hy => hws y (List.mem_cons_of_mem _ hy)) e h3
    refine ErrClaim.of_twin hcl fun ce hce => ?_
    rw [hpre]
    simp only [StateT.run_bind, hrun2]
    exact hce
  | ok q3 =>
    obtain ⟨r3, m3⟩ := q3
    rw [h3, cbagE.k_check_block_agree.arm1] at he; cases he

end sims

end L.Ind
