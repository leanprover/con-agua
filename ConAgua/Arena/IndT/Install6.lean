import ConAgua.Arena.IndT.Install5
import ConAgua.Arena.IndInstallSpec20
import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.IndInstallSpec19

/-!
# `checkAbsCtorSorts`, `checkAbsCtorSortsAll` under `StageC` (lane `indstaget`)

The fields' universes at the holes, from `StageC` and con-ron's preconditions of
`checkAbsCtorSorts_specF` (the context, the constructors and their normal forms denote, the
normal forms scoped at the holes' depth, the environment denotes), the twin side transcribed from
that spec's proof: the level-parameter test (the stub's `StageR` contract;
`allLevelParamsDefined_run` and `coreStep_of_store` for the step), the holes' depth (L only), the
fields opened at the holes (`openPisAtFvarsF_run`), their sorts (`installSimFsortsC`, con-ron's
`checkStructFieldSortsI_spec` on its run for the `CoreStep`).
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
  (hOpf : OpfF p) (hLC : LvlCacheProg p) (hLT : p.lookup "lv_leq_top" = some lvLeqTop) (hApd : ApdF p)

include hq henv hOpf hLC hLT in
/-- **`check_abs_ctor_sorts_one` under `StageC`** (twin side: one constructor of con-ron's
`checkAbsCtorSorts_specF`'s proof, after the level test). -/
theorem iaoW_simC (hsum : SumProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {ctx isP nF tyN hi : Word} {c : NestCtx} {b : Bool}
    (hC : StageC dn vis fe env m a) (hA : AbsOK m) (hc : DecB (fun m => decCtx m ctx.toNat) m c)
    (hty : H tyN) (hhi : hi.toNat = c.hiAt 0) (hb : (isP != 0) = b)
    {tyNP : ConLeche.Expr} {sortP : ConLeche.Level}
    (htyP : denoteE a.store (decI tyN) = some tyNP) (hW : ConLeche.Expr.WScoped (c.hiAt 0) tyNP)
    (hsP : denoteL a.store.ls c.sort = some sortP) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (iaoW p n m vis ctx isP nF tyN hi) (absOneAM fe c b nF.toNat (decI tyN)) a
      (fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  have hS := hC.stage
  obtain ⟨hs32, hse⟩ := installCtxWord9 hc hS.2.2.2.1
  unfold iaoW absOneAM
  split
  · exact Sim.of_none
  rename_i hov
  refine Sim.bindK (K := iaoK1 p n vis isP nF hi (rdW (m.arr64 IW) (ctx + 9)))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none else iaoK2 (callW p n "check_struct_field_sorts_i"
      [vis, isP, 0, rdW (m.arr64 IW) (ctx + 9), hi, r1.tail.headD 0, r1.tail.tail.headD 0, 0, 0, nF] m1))
    (by simp [iaoK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iaoK1_none p n m₁ _ _ _ _ _ r h, ite_eq_left h]
      · rw [iaoK1_some p n m₁ _ _ _ _ _ r h, ite_eq_right h])
    (by
      have h := opfSimRA (n := n) (k := nF) (i := hi) hOpf hty hS hA
      rw [hhi] at h
      exact h) ?_
  rintro r1 x1 m1 a1 ⟨⟨⟨hS1, hg1, hd1⟩, hr1⟩, hA1⟩
  obtain ⟨p1, ho1⟩ := ConRon.Bridge.Inductives.openPisAtFvarsF_run hC.check.state htyP hr1
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_pstep hS1 hA1 p1
  cases x1 with
  | none =>
    have h0 : r1.headD 0 = 0 := hd1
    simp only [h0, ite_true]; exact Sim.of_none
  | some fb =>
  obtain ⟨fvs, body⟩ := fb
  obtain ⟨xsP, xP, hxq, hxs, -⟩ := ConRon.Bridge.Inductives.denoteOpen_some_inv ho1
  obtain ⟨h1', hfv, -⟩ := hd1
  obtain ⟨hfd, hfb⟩ := hfv
  have g1 : r1.getD 1 0 = r1.tail.headD 0 := by rcases r1 with _ | ⟨_, _ | ⟨_, _⟩⟩ <;> rfl
  have g2 : r1.getD (1 + 1) 0 = r1.tail.tail.headD 0 := by
    rcases r1 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩ <;> rfl
  rw [g1, g2] at hfd hfb
  simp only [h1', show (1 : Word) ≠ 0 by decide, ite_false]
  show Sim _ (checkStructFieldSortsI V fe b false c.sort (c.hiAt 0) fvs [] nF.toNat >>= fun _ => pure ()) a1 _
  have hfvsc := ConRon.Bridge.Inductives.openers_typeD_WScoped hxq hW
  refine Sim.bindK (K := iaoK2) (body := fun _ m2 => some ([0], m2)) rfl (fun _ _ => rfl)
    (by
      have h := installSimFsortsC (dn := dn) (fe := fe) hq henv hLC hLT hsum n hn isP 0
        (rdW (m.arr64 IW) (ctx + 9)) hi _ _ 0 0 nF hs32 fvs [] hC1 hA1
        (by rw [hse]; exact ConRon.Bridge.denoteL_ext hsP p1.ext) hfd hfb
        (by simp [decHL, hslice?]) (by simp)
        (by rw [← partsAddNoOv hov]; exact UInt64.toNat_lt _) hxs
        (fun i _ x hx => by rw [hhi]; exact hfvsc i x hx)
      rw [hse, hhi, hb, show ((0 : Word) != 0) = false from rfl] at h
      exact Sim.withRunC h) ?_
  rintro r2 _ m2 a2 ⟨⟨hC2, hg2, -, -, hA2⟩, hr2⟩
  obtain ⟨c2, -⟩ := ConRon.Bridge.Inductives.checkStructFieldSortsI_spec fe
    (ConRon.Bridge.CoreSpec.of_core rfl) henv b false c.sort sortP (c.hiAt 0) fvs [] xsP [] nF.toNat
    (fun i _ x hx => hfvsc i x hx) a1 a2 _ hC1.check
    ⟨ConRon.Bridge.denoteL_ext hsP p1.ext, hxs, rfl, ConRon.Bridge.denoteFEnv_mono p1.ext hfe⟩ hr2
  exact Sim.ret ⟨hC2, hg1.trans hg2, hA2, (p1.toCore hC.check).trans c2⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts` under `StageC`** (twin side: con-ron's `checkAbsCtorSorts_specF`'s
proof). -/
theorem iacW_simC (hP : AbsProg p) (ctx isP : Word) (c : NestCtx) (b : Bool) (hb : (isP != 0) = b)
    (hhi : c.hiAt 0 < 2 ^ 64) {ctxP : ConLeche.NestCtx} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (co cl oo ol : Word) (cs : List (IConstantVal × Nat))
      (os : List (List NestFieldKind × EIdx)) (csP : List (ConLeche.ConstantVal × Nat))
      (osP : List (List ConLeche.NestFieldKind × ConLeche.Expr)),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCN cs co cl m → PSlR0 decKE os oo ol m →
    ConRon.Bridge.Inductives.dCtx a.store ctxP.find? c = some ctxP →
    ConRon.Bridge.Inductives.dCtors a.store cs = some csP →
    os.mapM (ConRon.Bridge.Inductives.dOut a.store) = some osP →
    (∀ o ∈ osP, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    Sim (iacW p n m vis ctx isP co cl oo ol) (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a
      (fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  induction n with
  | zero => intros; rw [iacW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a co cl oo ol cs os csP osP hC hA hc hcs hos hctxP hcsP hosP hws hfe
  have hS := hC.stage
  by_cases hcl : cl = 0
  · rw [iacW_nil1 p n m vis ctx isP co cl oo ol hcl, hcs.nil hcl]
    exact Sim.ret ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  by_cases hol : ol = 0
  · rw [iacW_nil2 p n m vis ctx isP co cl oo ol hcl hol, hos.nil hol]
    have : ConRon.Arena.checkAbsCtorSorts V fe c b cs [] = pure () := by
      cases cs <;> simp [ConRon.Arena.checkAbsCtorSorts]
    rw [this]
    exact Sim.ret ⟨hC, IWGrow.refl m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨qc, ⟨cv, nF⟩, cs', rfl, hwc, hqcb, hdc, hcs'⟩ := partsPSl_cons (hcs.pslr hcl) hcl
  obtain ⟨qo, ⟨ks, e⟩, os', rfl, hwo, hqob, hdo, hos'⟩ := partsPSl_cons (hos.pslr hol) hol
  obtain ⟨cP, csP', rfl, hcP, hcsP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcsP
  obtain ⟨oP, osP', rfl, hoP, hosP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hosP
  obtain ⟨tyNP, htyNP, rfl⟩ : ∃ tyN, denoteE a.store e = some tyN ∧ oP = (ks.map ConRon.Bridge.Inductives.kindOf, tyN) := by
    simp only [ConRon.Bridge.Inductives.dOut, Option.map_eq_some_iff] at hoP
    obtain ⟨x, hx, rfl⟩ := hoP
    exact ⟨x, hx, rfl⟩
  have hWP : ConLeche.Expr.WScoped (ctxP.hiAt 0) tyNP := hws _ List.mem_cons_self
  obtain ⟨namesP, lpsP, paramsP, sortP, hceq, hnm, hlp, -, hsort, -⟩ := ConRon.Bridge.Inductives.dCtx_inv hctxP
  have hhiP : c.hiAt 0 = ctxP.hiAt 0 := by
    rw [hceq]
    simp [ConRon.Arena.NestCtx.hiAt, ConLeche.NestCtx.hiAt, ConRon.Bridge.denoteNList_length _ _ hnm]
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  -- the words read
  have hcT : decCtx (truncM m) ctx.toNat = some c := hc
  obtain ⟨-, hlps, hnP, -, -, -, -⟩ := decCtx_some hcT
  obtain ⟨lo, ll, hlo, hll, hlpsd⟩ := decAt_some hlps
  have hlolt := partsIwLt hll
  obtain ⟨hwlo, hlob, -⟩ := partsIwRd hlo (w := ctx + 2) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨hwll, hllb, -⟩ := partsIwRd hll (w := ctx + 3) (by rw [UInt64.toNat_add]; simp; omega)
  have hdoT : decKE (truncM m) qo = some (ks, e) := hdo
  simp only [decKE, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, Prod.mk.injEq] at hdoT
  obtain ⟨-, -, ee, hee, -, rfl⟩ := hdoT
  obtain ⟨heelt, hee'⟩ := rec2IwH_trunc hee
  obtain ⟨ew, hew, hew32, hewe⟩ := iwH_rdW_at (w := UInt64.ofNat qo) (k := 2) (by rw [hqo']; exact hee')
    hS.2.2.2.1
  rw [show (UInt64.ofNat 2 : Word) = 2 from rfl] at hew
  rw [iacW_cons p n m vis ctx isP co cl oo ol hcl hol, hwc, hwo, hwlo, hwll, hew]
  simp only [ConRon.Arena.checkAbsCtorSorts]
  have hlpsm : decHL m (UInt64.ofNat lo : Word).toNat (UInt64.ofNat ll : Word).toNat = some c.lps := by
    rw [UInt64.toNat_ofNat_of_lt' hlob, UInt64.toNat_ofNat_of_lt' hllb]
    exact DecB.get (f := fun m => (decHL m lo ll : Option (List NIdx))) (OMono.decHL _ _) hlpsd
  have hl' : Frontend.denoteNList a.store.ns c.lps = some ctxP.lps := by rw [hceq]; exact hlp
  have hsort' : denoteL a.store.ls c.sort = some ctxP.sort := by rw [hceq]; exact hsort
  refine Sim.bindK (K := iacK1 p n vis ctx isP co cl oo ol (UInt64.ofNat qc) (UInt64.ofNat qo))
    (body := fun r1 m1 => if r1.headD 0 = 0 then none
      else iacK2 p n vis ctx isP co cl oo ol (UInt64.ofNat qc) (UInt64.ofNat qo)
        (callW p n "nest_ctx_hi_at" [ctx, 0] m1)) (by simp [iacK1])
    (fun r m₁ => by
      by_cases h : r.headD 0 = 0
      · rw [iacK1_none p n m₁ _ _ _ _ _ _ _ _ _ r h, ite_eq_left h]
      · rw [iacK1_some p n m₁ _ _ _ _ _ _ _ _ _ r h, ite_eq_right h])
    (by
      have h := apdCall_simR hApd n (UInt64.ofNat lo) (UInt64.ofNat ll) ew hew32 c.lps hS hA
        hC.check.state hlpsm ⟨_, denoteNList_mapM hl'⟩
      rw [hewe] at h
      exact Sim.withRunC h) ?_
  rintro r1 ok m1 a1 ⟨⟨hS1, hg1, ⟨hok1, -⟩, hA1, -⟩, hr1⟩
  obtain ⟨h1s, h1c, h1p, -⟩ := ConRon.Bridge.allLevelParamsDefined_run hC.check.state hl' htyNP hr1
  have c1 := ConRon.Bridge.Inductives.BI.coreStep_of_store hC.check h1s h1c h1p
  have hC1 : StageC dn vis fe env m1 a1 := hC.of_check hS1 hA1 c1.ok c1.ext
  by_cases h0 : r1.headD 0 = 0
  · simp only [h0, ite_true]; exact Sim.of_none
  have hokt : ok = true := by rw [← hok1]; simp only [bne_iff_ne, ne_eq, h0, not_false_eq_true]
  subst hokt
  simp only [h0, ite_false]
  rw [ite_eq_left trivial]
  -- `NestCtx.hiAt`
  have hc1 : decCtx m1 ctx.toNat = some c := hc.stab (decCtx_mono _) m1 hg1
  have hnPlt := partsIwLt hnP
  refine Sim.mstep (K := iacK2 p n vis ctx isP co cl oo ol (UInt64.ofNat qc) (UInt64.ofNat qo))
    (by simp [iacK2]) (fun r m₁ => iacK2_some p n m₁ vis ctx isP co cl oo ol _ _ r) fun r2 m2 h2 => ?_
  obtain ⟨s2, hs2, hpost2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (nestCtxHiAt_refines p hP.hiAt n _ ctx 0 c hc1 (by omega) (by omega)) h2
  obtain ⟨rfl, hr2⟩ := hpost2
  simp only at hs2; subst hs2
  rw [hr2]
  -- the constructor's fields
  have hdcT : decCN (truncM m) qc = some (cv, nF) := hdc
  obtain ⟨-, hnF⟩ := decCN_some hdcT
  have hnFlt := partsIwLt hnF
  obtain ⟨hwnF, hnFb, -⟩ := partsIwRd hnF (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  have hwnF1 : rdW (m1.arr64 IW) (UInt64.ofNat qc + 1) = UInt64.ofNat nF := by
    rw [← hwnF]; simp only [rdW]; rw [show (UInt64.ofNat qc + 1 : Word).toNat = qc + 1 by
      rw [UInt64.toNat_add, hqc']; simp; omega, hg1.2.2.1 _ hnFlt]
  have hwe1 : rdW (m1.arr64 IW) (UInt64.ofNat qo + 2) = ew := by
    rw [← hew]; simp only [rdW]; rw [show (UInt64.ofNat qo + 2 : Word).toNat = qo + 2 by
      rw [UInt64.toNat_add, hqo']; simp; omega, hg1.2.2.1 _ heelt]
  rw [hwnF1, hwe1]
  refine Sim.congr (op := absOneAM fe c b nF ee >>= fun _ => ConRon.Arena.checkAbsCtorSorts V fe c b cs' os')
    ?_ (by simp only [absOneAM, bind_assoc, pure_bind])
  have hhiw : (UInt64.ofNat (c.hiAt 0) : Word).toNat = c.hiAt 0 := UInt64.toNat_ofNat_of_lt' hhi
  have htyP1 : denoteE a1.store (decI ew) = some tyNP := by
    rw [hewe]; exact ConRon.Bridge.denote_ext htyNP c1.ext
  rcases n with _ | k
  · rw [callW_zero]; simp only [iacK3]; exact Sim.of_none
  refine Sim.bindK (K := iacK3 p (k + 1) vis ctx isP co cl oo ol) (body := fun _ m3 => iacK4
      (iacW p (k + 1) m3 vis ctx isP (co + 1) (cl - 1) (oo + 1) (ol - 1))) (by simp [iacK3])
      (fun r m₁ => iacK3_some p (k + 1) m₁ vis ctx isP co cl oo ol r)
    (Q := fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m1 m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a1 a')
    (fun r m' e => by
      obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
        (iao_spec p hP.one k _ vis ctx isP (UInt64.ofNat nF) ew (UInt64.ofNat (c.hiAt 0))) e
      have := iaoW_simC (p := p) hq henv hOpf hLC hLT hP.sum k (by omega) hC1 hA1 (hc.grow (decCtx_mono _) hg1) hew32
        hhiw hb htyP1 (by rw [hhiP]; exact hWP) (ConRon.Bridge.denoteL_ext hsort' c1.ext)
        (ConRon.Bridge.denoteFEnv_mono c1.ext hfe) r s'.mem hW
      rw [UInt64.toNat_ofNat_of_lt' hnFb, hewe] at this; dsimp only at this; exact this) ?_
  rintro _ _ m3 a3 ⟨hC3, hg3, hA3, c3⟩
  have hg13 := hg1.trans hg3
  have c13 := c1.trans c3
  have hcP' : ConRon.Bridge.Inductives.dCtors a3.store cs' = some csP' :=
    ConRon.Bridge.Inductives.dCtors_ext c13.ext _ _ hcsP'
  refine Sim.post (K := iacK4) rfl (fun _ _ => rfl)
    (ih (by omega) m3 a3 (co + 1) (cl - 1) (oo + 1) (ol - 1) cs' os' csP' osP' hC3 hA3
      (hc.grow (decCtx_mono _) hg13)
      (PSlR0.grow decCN_mono (⟨hcs'.1, Or.inr hcs'.2⟩ : PSlR0 decCN cs' (co + 1) (cl - 1) m) hg13)
      (PSlR0.grow decKE_mono (⟨hos'.1, Or.inr hos'.2⟩ : PSlR0 decKE os' (oo + 1) (ol - 1) m) hg13)
      (ConRon.Bridge.Inductives.dCtx_ext _ c13.ext _ _ hctxP) hcP'
      (ConRon.Bridge.Inductives.dOut_ext.list c13.ext _ _ hosP')
      (fun y hy => hws y (List.mem_cons_of_mem _ hy)) (ConRon.Bridge.denoteFEnv_mono c13.ext hfe)) ?_
  rintro _ _ _ _ ⟨hC4, hg4, hA4, c4⟩
  exact ⟨hC4, hg13.trans hg4, hA4, c13.trans c4⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts` refines `checkAbsCtorSorts`** under `StageC` (the denotations as
con-ron's `checkAbsCtorSorts_specF` asks): the context decoded below the tops with its holes'
bound below `2^64`, the constructors and their normal forms slices decoded below the tops. -/
@[refines ConRon.Arena.checkAbsCtorSorts]
theorem checkAbsCtorSorts_refinesC (hP : AbsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (ctx isP co cl oo ol : Word)
    (c : NestCtx) (b : Bool) (cs : List (IConstantVal × Nat)) (os : List (List NestFieldKind × EIdx))
    (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64) (hC : StageC dn vis fe env s₀.mem a₀)
    (hA : AbsOK s₀.mem)
    (hc : DecB (fun m => decCtx m ctx.toNat) s₀.mem c) (hcs : PSlR0 decCN cs co cl s₀.mem)
    (hos : PSlR0 decKE os oo ol s₀.mem) {ctxP : ConLeche.NestCtx}
    {csP : List (ConLeche.ConstantVal × Nat)}
    {osP : List (List ConLeche.NestFieldKind × ConLeche.Expr)}
    (hctxP : ConRon.Bridge.Inductives.dCtx a₀.store ctxP.find? c = some ctxP)
    (hcsP : ConRon.Bridge.Inductives.dCtors a₀.store cs = some csP)
    (hosP : os.mapM (ConRon.Bridge.Inductives.dOut a₀.store) = some osP)
    (hws : ∀ o ∈ osP, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts" [vis, ctx, isP, co, cl, oo, ol]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkAbsCtorSorts V fe c b cs os) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (iac_spec p hP.abs n s₀ vis ctx isP co cl oo ol) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hC', hg, hA', _⟩ := Sim.run (iacW_simC hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n hn _ a₀ co cl oo ol
      cs os csP osP hC hA hc hcs hos hctxP hcsP hosP hws hfe) hm
    ⟨hl, hok, hC', hg, hA'⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts_all` under `StageC`** (twin side: con-ron's
`checkAbsCtorSortsAll_specF`'s proof). -/
theorem iaaW_simC (hP : AbsProg p) (ctx isP : Word) (c : NestCtx) (b : Bool) (hb : (isP != 0) = b)
    (hhi : c.hiAt 0 < 2 ^ 64) {ctxP : ConLeche.NestCtx} (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (so sl oo ol : Word) (css : List (List (IConstantVal × Nat)))
      (oss : List (List (List NestFieldKind × EIdx))) (cssP : List (List (ConLeche.ConstantVal × Nat)))
      (ossP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))),
    StageC dn vis fe env m a → AbsOK m → DecB (fun m => decCtx m ctx.toNat) m c →
    PSlR0 decCNS css so sl m → PSlR0 decKES oss oo ol m →
    ConRon.Bridge.Inductives.dCtx a.store ctxP.find? c = some ctxP →
    css.mapM (ConRon.Bridge.Inductives.dCtors a.store) = some cssP →
    ConRon.Bridge.Inductives.dOutss a.store oss = some ossP →
    (∀ os ∈ ossP, ∀ o ∈ os, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2) →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    Sim (iaaW p n m vis ctx isP so sl oo ol) (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a
      (fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m') := by
  induction n with
  | zero => intros; rw [iaaW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a so sl oo ol css oss cssP ossP hC hA hc hcss hoss hctxP hcssP hossP hws hfe
  have hS := hC.stage
  by_cases hsl : sl = 0
  · rw [iaaW_nil1 p n m vis ctx isP so sl oo ol hsl, hcss.nil hsl]
    exact Sim.ret ⟨hC, IWGrow.refl m, hA⟩
  by_cases hol : ol = 0
  · rw [iaaW_nil2 p n m vis ctx isP so sl oo ol hsl hol, hoss.nil hol]
    have : ConRon.Arena.checkAbsCtorSortsAll V fe c b css [] = pure () := by
      cases css <;> simp [ConRon.Arena.checkAbsCtorSortsAll]
    rw [this]
    exact Sim.ret ⟨hC, IWGrow.refl m, hA⟩
  obtain ⟨qc, cs, css', rfl, hwc, hqcb, hdc, hcss'⟩ := partsPSl_cons (hcss.pslr hsl) hsl
  obtain ⟨qo, os, oss', rfl, hwo, hqob, hdo, hoss'⟩ := partsPSl_cons (hoss.pslr hol) hol
  obtain ⟨csP, cssP', rfl, hcP, hcssP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hcssP
  simp only [ConRon.Bridge.Inductives.dOutss] at hossP
  obtain ⟨osP, ossP', rfl, hoP, hossP'⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hossP
  have hqc' : (UInt64.ofNat qc : Word).toNat = qc := UInt64.toNat_ofNat_of_lt' hqcb
  have hqo' : (UInt64.ofNat qo : Word).toNat = qo := UInt64.toNat_ofNat_of_lt' hqob
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨co, cl, hco, hcl, hcd, hcb⟩ := partsAt decCN_mono (show decAt (truncM m)
    (decPL (truncM m) (decCN (truncM m))) qc = some cs from hdc)
  obtain ⟨oo2, ol2, hoo, hol2, hod, hob⟩ := partsAt decKE_mono (show decAt (truncM m)
    (decPL (truncM m) (decKE (truncM m))) qo = some os from hdo)
  have l1 := partsIwLt hcl; have l2 := partsIwLt hol2
  obtain ⟨w1, -, -⟩ := partsIwRd hco (w := UInt64.ofNat qc) hqc'
  obtain ⟨w2, -, -⟩ := partsIwRd hcl (w := UInt64.ofNat qc + 1) (by rw [UInt64.toNat_add, hqc']; simp; omega)
  obtain ⟨w3, -, -⟩ := partsIwRd hoo (w := UInt64.ofNat qo) hqo'
  obtain ⟨w4, -, -⟩ := partsIwRd hol2 (w := UInt64.ofNat qo + 1) (by rw [UInt64.toNat_add, hqo']; simp; omega)
  rw [UInt64.ofNat_toNat] at w1 w2 w3 w4
  rw [iaaW_cons p n m vis ctx isP so sl oo ol hsl hol, hwc, hwo, w1, w2, w3, w4]
  simp only [ConRon.Arena.checkAbsCtorSortsAll]
  refine Sim.bindK (K := iaaK1 p n vis ctx isP so sl oo ol) (body := fun _ m1 => iaaK2
      (iaaW p n m1 vis ctx isP (so + 1) (sl - 1) (oo + 1) (ol - 1))) (by simp [iaaK1])
      (fun r m₁ => iaaK1_some p n m₁ vis ctx isP so sl oo ol r)
    (Q := fun _ _ m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a')
    (fun r m' e => iacW_simC hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n (by omega) m a co cl oo2 ol2 cs os csP osP hC hA
      hc ⟨hcd, hcb⟩ ⟨hod, hob⟩ hctxP hcP hoP (hws osP List.mem_cons_self) hfe r m' (by
        obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (iac_spec p hP.abs n _ vis ctx isP co cl oo2 ol2) e
        exact hW)) ?_
  rintro _ _ m1 a1 ⟨hC1, hg1, hA1, c1⟩
  refine Sim.post (K := iaaK2) rfl (fun _ _ => rfl)
    (ih (by omega) m1 a1 (so + 1) (sl - 1) (oo + 1) (ol - 1) css' oss' cssP' ossP' hC1 hA1
      (hc.grow (decCtx_mono _) hg1)
      (PSlR0.grow decCNS_mono (⟨hcss'.1, Or.inr hcss'.2⟩ : PSlR0 decCNS css' (so + 1) (sl - 1) m) hg1)
      (PSlR0.grow (fun q => OMono.decAt (fun o l => OMono.decPL decKE_mono o l) q)
        (⟨hoss'.1, Or.inr hoss'.2⟩ : PSlR0 decKES oss' (oo + 1) (ol - 1) m) hg1)
      (ConRon.Bridge.Inductives.dCtx_ext _ c1.ext _ _ hctxP)
      (ConRon.Bridge.Inductives.dCtors_ext.list c1.ext _ _ hcssP')
      (ConRon.Bridge.Inductives.dOutss_ext c1.ext _ _ hossP')
      (fun y hy => hws y (List.mem_cons_of_mem _ hy)) (ConRon.Bridge.denoteFEnv_mono c1.ext hfe)) ?_
  rintro _ _ _ _ ⟨hC2, hg2, hA2⟩
  exact ⟨hC2, hg1.trans hg2, hA2⟩

include hq henv hOpf hLC hLT hApd in
/-- **`check_abs_ctor_sorts_all` refines `checkAbsCtorSortsAll`** under `StageC` (the denotations
as con-ron's `checkAbsCtorSortsAll_specF` asks): every member's constructors and normal forms as
slices of `[off, len]` pointers decoded below the tops. -/
@[refines ConRon.Arena.checkAbsCtorSortsAll]
theorem checkAbsCtorSortsAll_refinesC (hP : AbsProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (ctx isP so sl oo ol : Word)
    (c : NestCtx) (b : Bool) (css : List (List (IConstantVal × Nat)))
    (oss : List (List (List NestFieldKind × EIdx))) (hb : (isP != 0) = b) (hhi : c.hiAt 0 < 2 ^ 64)
    (hC : StageC dn vis fe env s₀.mem a₀) (hA : AbsOK s₀.mem)
    (hc : DecB (fun m => decCtx m ctx.toNat) s₀.mem c)
    (hcss : PSlR0 decCNS css so sl s₀.mem) (hoss : PSlR0 decKES oss oo ol s₀.mem)
    {ctxP : ConLeche.NestCtx} {cssP : List (List (ConLeche.ConstantVal × Nat))}
    {ossP : List (List (List ConLeche.NestFieldKind × ConLeche.Expr))}
    (hctxP : ConRon.Bridge.Inductives.dCtx a₀.store ctxP.find? c = some ctxP)
    (hcssP : css.mapM (ConRon.Bridge.Inductives.dCtors a₀.store) = some cssP)
    (hossP : ConRon.Bridge.Inductives.dOutss a₀.store oss = some ossP)
    (hws : ∀ os ∈ ossP, ∀ o ∈ os, ConLeche.Expr.WScoped (ctxP.hiAt 0) o.2)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_abs_ctor_sorts_all" [vis, ctx, isP, so, sl, oo, ol]
    ⦃fun _ s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkAbsCtorSortsAll V fe c b css oss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (iaa_spec p hP.all n s₀ vis ctx isP so sl oo ol) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (iaaW_simC hq henv hOpf hLC hLT hApd hP ctx isP c b hb hhi n hn _ a₀ so sl oo ol css oss cssP ossP
      hC hA hc hcss hoss hctxP hcssP hossP hws hfe) hm
    ⟨hl, hok, hQ⟩

end sims

end L.Ind
