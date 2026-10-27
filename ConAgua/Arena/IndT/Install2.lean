import ConAgua.Arena.IndT.Install1
import ConRon.Bridge.Inductives.BlockInstall
import ConAgua.Arena.IndRealLvlC
import ConAgua.Arena.IndInstallSpec.IagW
import ConAgua.Arena.IndInstallSpec.InstallSimCall
import ConAgua.Arena.IndInstallSpec.InstallRec2Tele
import ConAgua.Arena.IndPartsSpec.PartsPSlCons

/-!
# `checkBlockAgree` under `StageC` (lane `indstaget`)

`check_block_agree_one`'s model at `realCall p`, from `StageC` and the denotations con-ron's
`checkBlockAgree_specF` asks (the member's stored type closed, member 0's opened telescope and its
annotations' scoping, the two sorts), its twin side transcribed from that spec's proof:
`openPisAtFvarsF` (`openPisAtFvarsF_run`: a `PStep`, the opened telescope's denotation),
`fvarTypeDs` (`fvarTypeDs_run`), `checkBlockDomsAt` (`domsW_simC`, con-ron's
`checkBlockDomsAt_specF` on its run for the `CoreStep`), `lvlEq?` (`lvlEq?_crun`).
`check_block_agree` walks the other members, member 0's telescope opened per member.
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`lvl_eq_fueled`, its `lvl_eq_c` the real call, under `StageC`** (`lveW_ok`'s statement with
`lvlEqC_simC` for the stub contract): an answer other than `0` is the twin's verdict. -/
theorem lveC_okC {p : Prog} (hcl : CoreStageClosed p) (hLC : LvlCacheProg p)
    {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {env : ConLeche.Env} {n : Nat}
    {m m' : Mem} {a : AState} {u v : Word} {r : List Word}
    (h : lveC (realCall p) n m u v = some (r, m')) (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hu : H u) (hv : H v) {lu lv : ConLeche.Level} (hdu : denoteL a.store.ls (decI u) = some lu)
    (hdv : denoteL a.store.ls (decI v) = some lv) :
    ∃ b a', (lvlEq? (decI u) (decI v)).run a = .ok (some b, a') ∧ StageC dn vis fe env m' a' ∧
      IWGrow m m' ∧ AbsOK m' ∧ PStep a a' ∧ r.headD 0 = (if b then 1 else 0) := by
  rcases n with _ | n
  · simp [lveC] at h
  simp only [lveC] at h
  rcases hs : realCall p n "lvl_eq_c" [u, v] m with _ | ⟨r1, m1⟩
  · simp [hs] at h
  simp only [hs] at h
  by_cases h0 : r1.headD 0 = 0
  · rw [ite_eq_left h0] at h; exact absurd h (by simp)
  rw [ite_eq_right h0] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  obtain ⟨x, a1, hrun, hC1, hg, hdec, hA1, hp⟩ :=
    lvlEqC_simC p hcl hLC n hC hA u v hu hv lu lv hdu hdv r1 m1 hs
  simp only [decLvlEq] at hdec
  cases x with
  | none => exact absurd hdec h0
  | some b =>
    refine ⟨b, a1, hrun, hC1, hg, hA1, hp, ?_⟩
    cases b <;> simp at hdec ⊢ <;> simp [hdec]

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hOpf : OpfF p) (hLC : LvlCacheProg p)

include hq henv hOpf hLC in
/-- **`check_block_agree_one` under `StageC`** (twin side: one member of con-ron's
`checkBlockAgree_specF`'s proof). -/
theorem agW_okC (n : Nat) (hn : n + 1 ≤ 2 ^ 62) (m m' : Mem)
    (a : AState) (nP fvs0O fvs0L s0 cvTa s : Word) (r : List Word) (cv : IConstantVal)
    (fvs0 : List EIdx)
    (h : agW (realCall p) (n + 1) m vis nP fvs0O fvs0L s0 cvTa s = some (r, m'))
    (hC : StageC dn vis fe env m a) (hA : AbsOK m)
    (hty : (rdW (m.arr64 EREC) (cvTa + 3)).toNat < 2 ^ 32 ∧ decI (rdW (m.arr64 EREC) (cvTa + 3)) = cv.type)
    (hfvs0 : decHL m fvs0O.toNat fvs0L.toNat = some fvs0)
    (hfot : fvs0O.toNat + fvs0L.toNat ≤ iwTop m) (hs : H s) (hs0 : H s0)
    {tyP : ConLeche.Expr} {xs0 : List ConLeche.Expr} {sP s0P : ConLeche.Level}
    (htyP : denoteE a.store cv.type = some tyP) (hwx : ConLeche.Expr.WScoped 0 tyP)
    (hxs0 : Frontend.denoteEList a.store fvs0 = some xs0)
    (hsc0 : ∀ (i : Nat) (x : ConLeche.Expr), xs0[i]? = some x →
      ConLeche.Expr.WScoped (0 + i) x.fvarTypeD)
    (hsP : denoteL a.store.ls (decI s) = some sP) (hs0P : denoteL a.store.ls (decI s0) = some s0P) :
    ∃ a', (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)).run a = .ok ((), a') ∧
      StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧ ConRon.Bridge.CoreStep V env fe a a' := by
  have hStage := hC.stage
  have hz : UInt64.toNat 0 = 0 := rfl
  simp only [agW, Nat.add_sub_cancel] at h
  rcases hra : realCall p n "open_pis_at_fvars_f" [nP, rdW (m.arr64 EREC) (cvTa + 3), 0] m with _ | ⟨ra, m1⟩
  · rw [hra] at h; simp [agK1] at h
  rw [hra] at h
  by_cases h0 : ra.headD 0 = 0
  · rw [agK1_abort0 (realCall p) n m1 _ _ _ _ _ _ ra h0] at h; simp at h
  by_cases hL : ra.tail.tail.headD 0 = fvs0L
  case neg => rw [agK1_abortL (realCall p) n m1 _ _ _ _ _ _ ra h0 hL] at h; simp at h
  rw [agK1_ok (realCall p) n m1 _ _ _ _ _ _ ra h0 hL] at h
  obtain ⟨x1, a1, hrun1, hSt1, hg1, hdec1, hA1⟩ := opfF_okRA hty.1 (callW_opfF hOpf hra) hStage hA
  have hdty : denoteE a.store (decI (rdW (m.arr64 EREC) (cvTa + 3))) = some tyP := by
    rw [hty.2]; exact htyP
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hdty hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hSt1 hA1 p1
  cases x1 with
  | none => exact absurd hdec1 h0
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xs1, b1, hq1, hxs1, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  rw [hz] at hq1
  obtain ⟨-, hrl1, -⟩ := hdec1
  simp only [decRL, show (1:Nat) + 1 = 2 from rfl, agGetD1, agGetD2] at hrl1
  obtain ⟨hfv1, hfvb1⟩ := hrl1
  have hlen1 := decHL_length m1 hfv1
  have hlen0 := decHL_length m hfvs0
  rw [hL] at hlen1
  rcases hrb : ftdsF m1 [fvs0O, fvs0L] with _ | ⟨rd, m2⟩
  · rw [hrb] at h; simp [agK2] at h
  rw [hrb, agK2_some] at h
  have hbound1 : fvs0O.toNat + fvs0L.toNat ≤ iwTop m1 := by have := hg1.1; omega
  obtain ⟨x2, a2, hrun2, hSt2, hg2, hdec2⟩ :=
    ftdsF_ok dn vis fe fvs0O fvs0L fvs0 m1 m2 a1 rd hrb
      ⟨hSt1, by rw [decHL_grow hg1 (by omega)]; exact hfvs0, fun _ => hbound1⟩
  obtain ⟨p2, hdoms⟩ := ConRon.Bridge.Inductives.fvarTypeDs_run fvs0 xs0 hC1.check.state
    (ConRon.Bridge.denoteEList_ext p1.ext _ _ hxs0) hrun2
  have hA2 := ftdsF_afr hrb hA1
  have hC2 : StageC dn vis fe env m2 a2 := hC1.of_pstep hSt2 hA2 p2
  simp only [decRL, show (0:Nat) + 1 = 1 from rfl, agGetD0, agGetD1] at hdec2
  obtain ⟨hdm2, hdb2⟩ := hdec2
  rcases hw : domsW (realCall p) n m2 vis 0 (ra.tail.headD 0) (ra.tail.tail.headD 0) (rd.headD 0)
      (rd.tail.headD 0) nP with _ | ⟨r3, m3⟩
  · rw [hw] at h; simp [agK3] at h
  rw [hw, agK3_some] at h
  obtain ⟨hjf, hjd⟩ := domsW_le hw
  have hlt1 := UInt64.toNat_lt (ra.tail.headD 0)
  have hlt2 := UInt64.toNat_lt (ra.tail.tail.headD 0)
  have hlt3 := UInt64.toNat_lt (rd.headD 0)
  have hlt4 := UInt64.toNat_lt (rd.tail.headD 0)
  have hltt : iwTop m2 < 2 ^ 64 := UInt64.toNat_lt _
  have hltt1 : iwTop m1 < 2 ^ 64 := UInt64.toNat_lt _
  have hc : ∀ (i : Nat) (x : ConLeche.Expr), xs1[i]? = some x →
      ConLeche.Expr.WScoped (0 + i) x.fvarTypeD :=
    ConRon.Bridge.Inductives.openers_typeD_WScoped hq1 hwx
  have ht : ∀ (i : Nat) (y : ConLeche.Expr), (xs0.map ConLeche.Expr.fvarTypeD)[i]? = some y →
      ConLeche.Expr.WScoped (0 + i) y := fun i y hy => by
    rw [List.getElem?_map] at hy
    obtain ⟨z, hz', rfl⟩ := Option.map_eq_some_iff.mp hy
    exact hsc0 i z hz'
  have hxs1' := ConRon.Bridge.denoteEList_ext p2.ext _ _ hxs1
  obtain ⟨u3, a3, hrun3, hC3, hg3, hA3⟩ := domsW_simC hq henv n (by omega) m2 a2 0 (ra.tail.headD 0)
    (ra.tail.tail.headD 0) (rd.headD 0) (rd.tail.headD 0) nP fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD)
    hC2 hA2 (by rw [decHL_grow hg2 hfvb1]; exact hfv1) hdm2 (by omega) (by omega)
    (by have := hg2.1; omega) (by omega) (by simp only [UInt64.toNat_zero, Nat.zero_add]; exact hlt2)
    hjf hjd hxs1' hdoms (fun i _ x y hx hy => ⟨hc i x hx, ht i y hy⟩) _ hw
  dsimp only at hC3 hg3 hA3
  rw [hz] at hrun3
  obtain ⟨c3, -⟩ := ConRon.Bridge.Inductives.checkBlockDomsAt_specF fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv 0 fvs x2 xs1 (xs0.map ConLeche.Expr.fvarTypeD) hc ht
    nP.toNat a2 a3 u3 hC2.check ⟨hxs1', hdoms⟩ hrun3
  rcases hl : lveC (realCall p) n m3 s s0 with _ | ⟨re, m4⟩
  · rw [hl] at h; simp [agK4] at h
  rw [hl] at h
  by_cases hre : re.headD 0 = 0
  · rw [agK4_abort (m1 := m4) (re := re) hre] at h; simp at h
  rw [agK4_ok (m1 := m4) (re := re) hre] at h
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  have hx03 := p1.ext.trans (p2.ext.trans c3.ext)
  obtain ⟨b, a4, hrun4, hC4, hg4, hA4, -, hbre⟩ := lveC_okC hq.closed hLC hl hC3 hA3 hs hs0
    (ConRon.Bridge.denoteL_ext hsP hx03) (ConRon.Bridge.denoteL_ext hs0P hx03)
  obtain ⟨c4, -⟩ := ConRon.Bridge.Inductives.lvlEq?_crun hC3.check
    (ConRon.Bridge.denoteL_ext hsP hx03) (ConRon.Bridge.denoteL_ext hs0P hx03) hrun4
  have hb : b = true := by
    cases b
    · exact absurd (by rw [hbre]; rfl) hre
    · rfl
  subst hb
  refine ⟨a4, ?_, hC4, (hg1.trans hg2).trans (hg3.trans hg4), hA4,
    ((p1.trans p2).toCore hC.check).trans (c3.trans c4)⟩
  have hty' : cv.type = decI (rdW (m.arr64 EREC) (cvTa + 3)) := hty.2.symm
  simp only [agreeBodyAM, unwrapOr, hty', StateT.run_bind]
  simp only [hz] at hrun1
  have heq : (fvs.length == fvs0.length) = true := by
    simp only [beq_iff_eq]; omega
  have hlenE : fvs.length = fvs0.length := by omega
  simp [StateT.run_bind, hrun1, hrun2, hrun3, hrun4, hlenE, liftFueled, exc_ok_bind]
  rfl

include hq henv hOpf hLC in
/-- **`check_block_agree_one` is one step of `checkBlockAgree`** under `StageC` (member 0's
telescope opened by the caller; the denotations as con-ron's `checkBlockAgree_specF`'s proof has
them at a member). -/
@[refines_part ConRon.Arena.checkBlockAgree "one member's two agreements"]
theorem checkBlockAgreeOne_refinesC
    (hd : p.lookup "check_block_doms_at" = some checkBlockDomsAt)
    (hl : p.lookup "lvl_eq_fueled" = some lvlEqFueled)
    (hp : p.lookup "check_block_agree_one" = some checkBlockAgreeOne) (had : AdF p) (n : Nat)
    (hn : n + 1 ≤ 2 ^ 62) (s₀ : St) (a₀ : AState) (nP fvs0O fvs0L s0 cvTa s : Word)
    (cv : IConstantVal) (fvs0 : List EIdx) (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hty : (rdW (s₀.mem.arr64 EREC) (cvTa + 3)).toNat < 2 ^ 32 ∧
      decI (rdW (s₀.mem.arr64 EREC) (cvTa + 3)) = cv.type)
    (hfvs0 : decHL s₀.mem fvs0O.toNat fvs0L.toNat = some fvs0)
    (hfot : fvs0O.toNat + fvs0L.toNat ≤ iwTop s₀.mem) (hs : H s) (hs0 : H s0)
    {tyP : ConLeche.Expr} {xs0 : List ConLeche.Expr} {sP s0P : ConLeche.Level}
    (htyP : denoteE a₀.store cv.type = some tyP) (hwx : ConLeche.Expr.WScoped 0 tyP)
    (hxs0 : Frontend.denoteEList a₀.store fvs0 = some xs0)
    (hsc0 : ∀ (i : Nat) (x : ConLeche.Expr), xs0[i]? = some x →
      ConLeche.Expr.WScoped (0 + i) x.fvarTypeD)
    (hsP : denoteL a₀.store.ls (decI s) = some sP) (hs0P : denoteL a₀.store.ls (decI s0) = some s0P) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_agree_one"
      [vis, nP, fvs0O, fvs0L, s0, cvTa, s]
    ⦃fun _r s' => LocEq s' s₀ ∧
      AM.ok (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ (AM.st (agreeBodyAM fe nP.toNat fvs0 cv (decI s) (decI s0)) a₀);
      ⊤⦄ := by
  refine triple_post (checkBlockAgreeOne_spec p hd hl hp had (realCall p) (realCall_spec p) (n + 1) s₀
    vis nP fvs0O fvs0L s0 cvTa s) ?_
  rintro r s' ⟨hlq, hm⟩
  obtain ⟨a', hrun, hC', hg, hA', hcs⟩ := agW_okC hq henv hOpf hLC n hn s₀.mem s'.mem a₀ nP fvs0O fvs0L s0 cvTa
    s r cv fvs0 hm hC hA hty hfvs0 hfot hs hs0 htyP hwx hxs0 hsc0 hsP hs0P
  obtain ⟨hok, hst, -⟩ := AM.of_run_ok _ _ _ _ hrun
  exact ⟨hlq, hok, by rw [hst]; exact hC', hg, hA', by rw [hst]; exact hcs⟩

include hq henv hOpf hLC in
/-- **`check_block_agree` under `StageC`** (twin side: con-ron's `checkBlockAgree_specF`'s proof;
member 0's telescope opened per member, as the twin does). -/
theorem iagW_simC (hP : AgreeProg p) (nP c0 s0 : Word) (cv0 : IConstantVal) {cv0P : ConLeche.ConstantVal}
    {s0P : ConLeche.Level} (h0 : ConLeche.Expr.WScoped 0 cv0P.type) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (rest : List (IConstantVal × LIdx))
      (cvsP : List (ConLeche.ConstantVal × ConLeche.Level)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCVp m c0.toNat) m cv0 → H s0 →
    PSlR decTele rest o l m →
    Frontend.denoteCV a.store cv0 = some cv0P → denoteL a.store.ls (decI s0) = some s0P →
    rest.mapM (ConRon.Bridge.Inductives.BI.dCvL a.store) = some cvsP →
    (∀ x ∈ cvsP, ConLeche.Expr.WScoped 0 x.1.type) →
    Sim (iagW p n m vis nP c0 s0 o l) (ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest) a
      (fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  induction n with
  | zero => intro m a o l rest _ _ _ _ _ _ _ _ _ _; rw [iagW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a o l rest cvsP hC hA hc0 hs0 hrest hc0P hs0P hcvs hws
  have hS := hC.stage
  by_cases hl : l = 0
  · rw [iagW_nil p n m vis nP c0 s0 o l hl]
    have : rest = [] := by
      have h := hrest.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, ⟨cvTa, sx⟩, rest', rfl, hw, hqb, hdx, hrest'⟩ := partsPSl_cons hrest hl
  obtain ⟨xP, restP, rfl, hx, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcvs
  obtain ⟨hxcv, hxs⟩ := ConRon.Bridge.Inductives.BI.dCvL_inv hx
  dsimp only at hxcv hxs
  have hwx : ConLeche.Expr.WScoped 0 xP.1.type := hws _ List.mem_cons_self
  rw [iagW_cons p n m vis nP c0 s0 o l hl, installAgree_cons]
  obtain ⟨hty0, htye0⟩ := partsCVType hc0 (w := c0) rfl
  have hd0 : denoteE a.store (decI (rdW (m.arr64 EREC) (c0 + 3))) = some cv0P.type := by
    rw [htye0]; exact ConRon.Bridge.denoteCV_type hc0P
  refine Sim.bindK (K := iagK1 p n vis nP c0 s0 o l) (body := fun r1 m1 => if r1.headD 0 = 0 then none
      else iagK2 p n vis nP c0 s0 o l (callW p n "check_block_agree_one" [vis, nP, r1.tail.headD 0,
        r1.tail.tail.headD 0, s0, rdW (m1.arr64 IW) (rdW (m1.arr64 IW) o),
        rdW (m1.arr64 IW) (rdW (m1.arr64 IW) o + 1)] m1)) (by simp [iagK1])
      (fun r m₁ => by
        by_cases h : r.headD 0 = 0
        · rw [iagK1_none p n m₁ vis nP c0 s0 o l r h, ite_eq_left h]
        · rw [iagK1_some p n m₁ vis nP c0 s0 o l r h, ite_eq_right h])
    (by
      have h := opfSimRA (n := n) (k := nP) (i := 0) hOpf hty0 hS hA
      rw [htye0] at h; exact h) ?_
  rintro r1 x1 m1 a1 ⟨⟨⟨hS1, hg1, hd1⟩, hrun1⟩, hA1⟩
  rw [← htye0] at hrun1
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state hd0 hrun1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, ite_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs0, body0⟩ := fb
  obtain ⟨xs0, b0, hq0, hxs0, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, ite_false]
  show Sim _ (agreeBodyAM fe nP.toNat fvs0 cvTa sx (decI s0) >>= fun _ =>
    ConRon.Arena.checkBlockAgree V fe nP.toNat cv0 (decI s0) rest') a1 _
  -- the member's record words, read in `m1`
  have hd1x : decTele (truncM m1) q = some (cvTa, sx) := hdx.grow (decTele_mono _) hg1
  simp only [decTele, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hd1x
  obtain ⟨c, hc, cvv, hcv, sv, hsv, rfl, rfl⟩ := hd1x
  have hT1 : iwTop m1 < 2 ^ 64 := (rdW (m1.arr64 CTL) 200).toNat_lt
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
  rw [hw1]
  obtain ⟨hwc, hcb, -⟩ := partsIwRd hc (w := UInt64.ofNat q) hq'
  obtain ⟨-, hsv'⟩ := rec2IwH_trunc hsv
  obtain ⟨v, hv, hv32, hve⟩ := iwH_rdW_at (w := UInt64.ofNat q) (k := 1) (by rw [hq']; exact hsv')
    hS1.2.2.2.1
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at hv
  rw [hwc, hv]
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hty := partsCVType hcv (w := UInt64.ofNat c) hc'
  rw [← hve]
  rw [← hve] at hxs
  have hxcv1 := ConRon.Bridge.denoteCV_ext hxcv p1.ext
  cases n with
  | zero =>
    rw [callW_zero]; simp only [iagK2]; exact Sim.of_none
  | succ k =>
  refine Sim.bindK (K := iagK2 p (k + 1) vis nP c0 s0 o l) (body := fun _ m2 =>
      iagK3 (iagW p (k + 1) m2 vis nP c0 s0 (o + 1) (l - 1))) (by simp [iagK2]) (fun _ _ => by simp [iagK2])
    (installSimCall
      (Q := fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m1 m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a1 a')
      (checkBlockAgreeOne_refinesC hq henv hOpf hLC hP.doms hP.lvl hP.one hP.ad k (by omega)
        ⟨m1, Locals.init []⟩ a1 nP _ _ s0 _ v cvv fvs0 hC1 hA1 hty hfd hfb hv32 hs0
        (ConRon.Bridge.denoteCV_type hxcv1) hwx hxs0
        (ConRon.Bridge.Inductives.openers_typeD_WScoped hq0 h0)
        (ConRon.Bridge.denoteL_ext hxs p1.ext) (ConRon.Bridge.denoteL_ext hs0P p1.ext))
      fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩) ?_
  rintro - - m2 a2 ⟨hC2, hg2, hA2, c2⟩
  have c02 := (p1.toCore hC.check).trans c2
  refine Sim.post (K := iagK3) rfl (fun _ _ => rfl)
    (ih (by omega) m2 a2 (o + 1) (l - 1) rest' restP hC2 hA2 (hc0.grow (OMono.decCVp _) (hg1.trans hg2))
      hs0 (hrest'.grow decTele_mono (hg1.trans hg2)) (ConRon.Bridge.denoteCV_ext hc0P c02.ext)
      (ConRon.Bridge.denoteL_ext hs0P c02.ext)
      (ConRon.Bridge.Inductives.BI.dCvL_ext.list c02.ext _ _ hrestP)
      (fun y hy => hws y (List.mem_cons_of_mem _ hy))) ?_
  rintro _ _ _ _ ⟨hC3, hg3, hA3, c3⟩
  exact ⟨hC3, (hg1.trans hg2).trans hg3, hA3, c02.trans c3⟩

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
  triple_post (iag_spec p hP.agree n s₀ vis nP c0 s0 o l) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (iagW_simC hq henv hOpf hLC hP nP c0 s0 cv0 h0 n hn _ a₀ o l rest cvsP hC hA hc0 hs0
      hrest hc0P hs0P hcvs hws) hm
    ⟨hl, hok, hQ.1, hQ.2.1, hQ.2.2.1⟩

end sims

end L.Ind
