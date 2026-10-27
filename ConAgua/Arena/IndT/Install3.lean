import ConAgua.Arena.IndT.Sum2
import ConAgua.Arena.IndT.Install1
import ConAgua.Arena.IndInstallSpec9

/-!
# `checkBlockTele`, `checkBlockTeles` under `StageC` (lane `indstaget`)

`check_block_tele`'s model, from `StageC` and con-ron's preconditions of `checkBlockTele_specF`
(the member denotes, the environment denotes), its twin side transcribed from that spec's proof:
`checkConstantVal` (the stub's `StageR` contract, `checkConstantVal_bridge` on its run for the
`CoreStep` and the stored type's closure), `checkSumTele` (`checkSumTele_refinesC`, con-ron's
`checkSumTele_spec` on its run for the answer's denotation), `stripPis` (`stripPis_pstep`), the
sort's intern (`internSortE_run`). `check_block_teles` walks the members (`dMember_ext`).
-/


open ConRon.Arena
open Std.WP
open scoped Lean.Order
open ConRon.Bridge.Inductives (PStep)

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- `TeleOut` under `StageC`: the checked former below the tops, its result sort a handle. -/
def TeleOutC (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (env : ConLeche.Env)
    (m : Mem) (r : List Word) (x : IConstantVal × LIdx) (m' : Mem) (a' : AState) : Prop :=
  StageC dn vis fe env m' a' ∧ IWGrow m m' ∧ decCVp m' (r.headD 0).toNat = some x.1 ∧
    CVExt m' (r.headD 0).toNat ∧ H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2

theorem TeleOutC.toR {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {env : ConLeche.Env} {m : Mem} {r : List Word} {x : IConstantVal × LIdx} {m' : Mem}
    {a' : AState} (h : TeleOutC dn vis fe env m r x m' a') : TeleOut dn vis fe m r x m' a' :=
  ⟨h.1.stage, h.2⟩

section sims
variable {p : Prog} (hq : KnotStageProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
  {fe : IFEnv} {env : ConLeche.Env} (henv : ConLeche.EnvWF env)
  (hV : ValProg p)
  (hApd : ApdF p) (hCrk : CrKeep p)

include hq henv hV hApd hCrk in
/-- `check_sum_tele` under `StageC` as a `Sim` of its call (the constant and the start record the
same, below the tops). -/
theorem installCstSimC (hP : CstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {cv k : Word} {cvv : IConstantVal} (hC : StageC dn vis fe env m a)
    (hcv : decCVp m cv.toNat = some cvv) (hx : CVExt m cv.toNat) (hA : AbsOK m)
    {cvP : ConLeche.ConstantVal} (hcvP : Frontend.denoteCV a.store cvv = some cvP)
    (hws : ConLeche.Expr.WScoped 0 cvP.type) (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (callW p n "check_sum_tele" [vis, cv, k, cv] m) (checkSumTele V fe cvv k.toNat cvv) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        decCVp m' (r.headD 0).toNat = some x.1 ∧ CVExt m' (r.headD 0).toNat ∧
        H (r.tail.headD 0) ∧ decI (r.tail.headD 0) = x.2 ∧ AbsOK m') :=
  installSimCall (checkSumTele_refinesC hq henv hV hApd hCrk hP.alloc hP.copy hP.cons hP.view hP.fvarFind hP.fvarPush
    hP.internFVar hP.wt hP.sortFind hP.sortPush hP.internSort hP.derB hP.forallFind hP.forallPush
    hP.internForall hP.mkForall hP.closeTele hP.erAlloc hP.cvNew hP.slow hP.i1 hP.ab hP.tele hP.strip
    n hn _ a cv k cv cvv cvv hC hcv hx.1 hx.2 hcv hx.1 hx.2 hA hcvP hcvP hws hfe)
    fun _ _ ⟨_, hok, hC', hg, hd, h32, hs, hb, hsl, hA'⟩ => ⟨hok, hC', hg, hd, ⟨hb, hsl⟩, h32, hs, hA'⟩

include hq henv hV hApd hCrk in
/-- **`check_block_tele` under `StageC`** (twin side: con-ron's `checkBlockTele_specF`'s proof). -/
theorem ibtW_simC (hP : CstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) {m : Mem} {a : AState}
    {nP ms : Word} {msh : MemberShape}
    (hC : StageC dn vis fe env m a) (hms : MemOK m ms.toNat msh) (hA : AbsOK m)
    {msP : ConLeche.MemberShape} (hmsP : ConRon.Bridge.Inductives.dMember a.store msh = some msP)
    (hfe : ConRon.Bridge.denoteFEnv a.store fe = some env) :
    Sim (ibtW p (n + 1) m vis nP ms) (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a
      (fun r x m' a' => TeleOutC dn vis fe env m r x m' a' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  have hS := hC.stage
  obtain ⟨hcvP, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hmsP
  obtain ⟨hmsB, hcx⟩ := hms
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  obtain ⟨⟨c, hc, hcv⟩, hni, -⟩ := decMS_some (m := truncM m) hmsB
  obtain ⟨hw0, hcb, hmsl⟩ := partsIwRd hc rfl
  obtain ⟨hw1, hnb, -⟩ := partsIwRd hni (w := ms + 1) (by rw [UInt64.toNat_add]; simp; omega)
  obtain ⟨-, hcN⟩ := rec2IwN_trunc hc
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  have hcvx : CVExt m (UInt64.ofNat c : Word).toNat := by rw [hc']; exact hcx c hcN
  have hcvm : decCVp m (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.get (OMono.decCVp _) hcv
  rw [ibtW.eq_2]
  rw [hw0, hw1]
  split
  · exact Sim.of_none
  rename_i hov
  have hk : (nP + UInt64.ofNat msh.nIdx).toNat = nP.toNat + msh.nIdx := by
    rw [partsAddNoOv hov, UInt64.toNat_ofNat_of_lt' hnb]
  unfold ConRon.Arena.checkBlockTele
  refine Sim.bindK (K := ibtW.k_check_constant_val p n vis _ _) (body := fun _ m1 => ibtW.k_check_sum_tele p n _
    (callW p n "check_sum_tele" [vis, UInt64.ofNat c, nP + UInt64.ofNat msh.nIdx, UInt64.ofNat c] m1))
    rfl (fun _ _ => rfl)
    (Sim.withFr (Sim.withRunC
      (installSimCall (Q := fun _ _ m' a' => StageT dn vis fe m' a' ∧ IWGrow m m')
        (checkConstantVal_refinesT p hV hq hApd hCrk n hn _ a dn fe vis _ msh.cvT hC.stageT
          (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK)
        fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2.1⟩))
      (fun _ _ e => checkConstantVal_absOK p hV hq hApd hCrk hn hC.stageT
        (rec2DecCV_erecP hcvm hcvx) (rec3CVExt_lt hS hcvx) (denoteCV_lps hcvP) hA.crMemo.crOK e hA)) ?_
  rintro _ _ m1 a1 ⟨⟨⟨hT1, hg1⟩, hr1⟩, hA1⟩
  have hS1 := hT1.stage
  obtain ⟨c1, F₁, hF₁⟩ := ConRon.Bridge.checkConstantVal_bridge rfl (ConRon.Bridge.CoreSpec.of_core rfl)
    hC.check henv hcvP hr1
  have hC1 : StageC dn vis fe env m1 a1 := StageC.of_T hT1 c1.ok
  have hcA := ConRon.Bridge.denoteCV_ext hcvP c1.ext
  have hw1' : ConLeche.Expr.WScoped 0 msP.cvT.type :=
    ConLeche.Expr.WScoped.of_not_hasFvar (ConLeche.checkConstantVal_typeWF hF₁).1
  have hcvm1 : decCVp m1 (UInt64.ofNat c : Word).toNat = some msh.cvT := by
    rw [hc']; exact DecB.stab (OMono.decCVp _) hcv m1 hg1
  refine Sim.bindK (K := ibtW.k_check_sum_tele p n _) (body := fun r2 m2 => ibtW.k_strip_pis p n (r2.headD 0) (r2.tail.headD 0)
      (callW p n "strip_pis" [nP + UInt64.ofNat msh.nIdx, rdW (m2.arr64 EREC) (r2.headD 0 + 3)] m2))
    rfl (fun _ _ => rfl) (by
      rw [← hk]
      exact Sim.withRunC (installCstSimC hq henv hV hApd hCrk hP n hn hC1 hcvm1 (CVExt_grow hg1 hcvx) hA1 hcA hw1'
        (ConRon.Bridge.denoteFEnv_mono c1.ext hfe))) ?_
  rintro r2 ⟨cvTa, sx⟩ m2 a2 ⟨⟨hC2, hg2, hcvTa, hxTa, hs32, hsd, hA2⟩, hr2⟩
  obtain ⟨c2, F₂, cvTaP, sP, -, h2a, h2b⟩ := ConRon.Bridge.Inductives.checkSumTele_spec fe rfl
    (ConRon.Bridge.CoreSpec.of_core rfl) henv msh.cvT msP.cvT (nP + UInt64.ofNat msh.nIdx).toNat msh.cvT
    msP.cvT hw1' a1 a2 _ hC1.check ⟨hcA, hcA, ConRon.Bridge.denoteFEnv_mono c1.ext hfe⟩ hr2
  dsimp only at h2a h2b
  have hS2 := hC2.stage
  obtain ⟨htyl, htye⟩ := partsCVType (installCvDecB hcvTa hxTa) (w := r2.headD 0) rfl
  refine Sim.bindK (K := ibtW.k_strip_pis p n _ _) (body := fun r3 m3 => if r3.headD 0 = 0 then none
      else ibtW.k_intern_sort p (r2.headD 0) (r2.tail.headD 0) (r3.tail.tail.tail.headD 0)
        (callW p n "intern_sort" [r2.tail.headD 0] m3)) rfl (fun _ _ => rfl)
    (by
      have h : Sim (callW p n "strip_pis" [nP + UInt64.ofNat msh.nIdx, rdW (m2.arr64 EREC) (r2.headD 0 + 3)] m2)
          _ a2 _ := fun r m' e =>
        stripF_pis_ok dn vis fe (nP + UInt64.ofNat msh.nIdx) _ htyl m2 m' a2 r (stripF_of_callW hP.strip e) hS2
      rw [hk, htye] at h
      exact Sim.withFr (Sim.withRunC h) (fun _ _ e => stripF_afr (stripF_of_callW hP.strip e) hA2)) ?_
  rintro r3 x3 m3 a3 ⟨⟨⟨hS3, hg3, hd3⟩, hr3⟩, hA3⟩
  obtain ⟨ha3, -⟩ := ConRon.Bridge.Inductives.stripPis_pstep hC2.check.state
    (ConRon.Bridge.denoteCV_type h2a) hr3
  rw [ha3] at hS3 ⊢
  have hC3 : StageC dn vis fe env m3 a2 := hC2.of_pstep hS3 hA3 (PStep.refl hC2.check.state)
  cases x3 with
  | none =>
    have h0 : r3.headD 0 = 0 := hd3
    simp only [h0, ite_true]; exact Sim.of_none
  | some bb =>
  obtain ⟨bs, body⟩ := bb
  obtain ⟨h1, -, hb32, hbe⟩ := hd3
  simp only [h1, show (1 : Word) ≠ 0 by decide, ite_false]
  have hd3' : (r3.drop 3).headD 0 = r3.tail.tail.tail.headD 0 := by
    rcases r3 with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, _⟩⟩⟩⟩ <;> rfl
  rw [hd3'] at hb32 hbe
  refine Sim.bindK (K := ibtW.k_intern_sort p _ _ _) (body := fun r4 m4 => if r3.tail.tail.tail.headD 0 = r4.headD 0
      then some ([r2.headD 0, r2.tail.headD 0], m4) else none) rfl (fun _ _ => rfl)
    (by
      have hsd' : decI (r2.tail.headD 0) = sx := hsd
      rw [← hsd']; exact Sim.withRunC (installSortSim hP n hS3 hs32)) ?_
  rintro r4 srt m4 a4 ⟨⟨hS4, hg4, hsrt, hf4⟩, hr4⟩
  have hsd' : decI (r2.tail.headD 0) = sx := hsd
  rw [hsd'] at hr4
  obtain ⟨p4, -⟩ := ConRon.Bridge.Inductives.internSortE_run hC3.check.state h2b hr4
  have hA4 := hf4 hA3
  have hC4 : StageC dn vis fe env m4 a4 := hC3.of_pstep hS4 hA4 p4
  split
  · rename_i heq
    have hb : (body == srt) = true := by rw [← hbe, ← hsrt, heq, decE_eq]; exact beq_self_eq_true _
    simp only [hb, ite_true]
    refine Sim.ret ⟨⟨hC4, ((hg1.trans hg2).trans hg3).trans hg4, ?_, ?_, hs32, hsd⟩, hA4,
      c1.trans (c2.trans (p4.toCore c2.ok))⟩
    · exact DecB.stab (OMono.decCVp _) (installCvDecB hcvTa hxTa) m4 (hg3.trans hg4)
    · exact CVExt_grow (hg3.trans hg4) hxTa
  · exact Sim.of_none

include hq henv hV hApd hCrk in
/-- **`check_block_tele` refines `checkBlockTele`** under `StageC` (the knot's core calls; the
member's denotation as con-ron's `checkBlockTele_specF` asks): the checked former below the tops,
its result sort a handle. -/
@[refines ConRon.Arena.checkBlockTele]
theorem checkBlockTele_refinesC (hP : CstProg p)
    (hp : p.lookup "check_block_tele" = some checkBlockTele) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP ms : Word) (msh : MemberShape)
    (hC : StageC dn vis fe env s₀.mem a₀) (hms : MemOK s₀.mem ms.toNat msh) (hA : AbsOK s₀.mem)
    {msP : ConLeche.MemberShape} (hmsP : ConRon.Bridge.Inductives.dMember a₀.store msh = some msP)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_tele" [vis, nP, ms]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀ ∧
      TeleOutC dn vis fe env s₀.mem r (AM.res (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) s'.mem
        (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀) ∧ AbsOK s'.mem ∧
      ConRon.Bridge.CoreStep V env fe a₀ (AM.st (ConRon.Arena.checkBlockTele V fe nP.toNat msh) a₀);
      ⊤⦄ :=
  triple_post (ibt_spec p hp (n + 1) s₀ vis nP ms) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ, hA', hc⟩ := Sim.run (ibtW_simC hq henv hV hApd hCrk hP n hn hC hms hA hmsP hfe) hm
    ⟨hl, hok, hQ, hA', hc⟩

include hq henv hV hApd hCrk in
/-- **`check_block_teles` under `StageC`** (twin side: con-ron's `checkBlockTeles_specF`'s
proof). -/
theorem ibtsW_simC (hP : InstProg p) (nP : Word) (n : Nat) (hn : n ≤ 2 ^ 62) :
    ∀ (m : Mem) (a : AState) (o l : Word) (mss : List MemberShape)
      (mssP : List ConLeche.MemberShape),
    StageC dn vis fe env m a → MemsOK m o l mss → AbsOK m →
    mss.mapM (ConRon.Bridge.Inductives.dMember a.store) = some mssP →
    ConRon.Bridge.denoteFEnv a.store fe = some env →
    Sim (ibtsW p n m vis nP o l) (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a
      (fun r x m' a' => StageC dn vis fe env m' a' ∧ IWGrow m m' ∧
        PSlR decTele x (r.headD 0) (r.tail.headD 0) m' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') := by
  induction n with
  | zero => intros; rw [ibtsW.eq_1]; exact Sim.of_none
  | succ n ih =>
  intro m a o l mss mssP hC hms hA hmssP hfe
  have hS := hC.stage
  by_cases hl : l = 0
  · rw [ibtsW.arm1 p n m vis nP o l hl]
    have : mss = [] := by
      have h := hms.1.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hC, IWGrow.refl m, PSlR.nil decTele m, hA, ConRon.Bridge.CoreStep.refl hC.check⟩
  obtain ⟨q, x, rest, rfl, hw, hqb, hmok, hrest⟩ := hms.cons hl
  obtain ⟨xP, restP, rfl, hxP, hrestP⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv hmssP
  rw [ibtsW.arm2 p n m vis nP o l hl, hw]
  unfold ConRon.Arena.checkBlockTeles
  rcases n with _ | k
  · rw [callW_zero]; rw [ibtsW.k_check_block_tele.none]; exact Sim.of_none
  refine Sim.bindK (K := ibtsW.k_check_block_tele p (k + 1) vis nP o l) (body := fun r1 m1 => ibtsW.k_rec2 p (k + 1) vis nP o l
      (callW p (k + 1) "rec2" [r1.headD 0, r1.tail.headD 0] m1)) (ibtsW.k_check_block_tele.none ..)
      (fun r m₁ => ibtsW.k_check_block_tele.arm1 p (k + 1) vis nP o l r m₁)
    (installSimCall (Q := fun r x m' a' => TeleOutC dn vis fe env m r x m' a' ∧ AbsOK m' ∧
        ConRon.Bridge.CoreStep V env fe a a') (checkBlockTele_refinesC hq henv hV hApd hCrk hP.toCstProg hP.bTele k (by omega)
      ⟨m, Locals.init []⟩ a nP _ x hC hmok hA hxP hfe) fun _ _ ⟨_, hok, hQ, hA', hc⟩ => ⟨hok, hQ, hA', hc⟩) ?_
  rintro r1 x1 m1 a1 ⟨hT1, hA1, c1⟩
  refine Sim.mstep (K := ibtsW.k_rec2 p (k + 1) vis nP o l) (ibtsW.k_rec2.none ..)
    (fun r m₁ => ibtsW.k_rec2.arm1 p (k + 1) vis nP o l r m₁) fun r2 m2 h2 => ?_
  obtain ⟨hS2, hg2, hd2, hlt2⟩ := installRec2Tele hP (k + 1) hT1.toR h2
  have hA2 : AbsOK m2 := by
    obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (rec2_specW p hP.alloc (k + 1) hP.rec2 _ _ _) h2
    exact recW_afr hW hA1
  have hC2 : StageC dn vis fe env m2 a1 := hT1.1.of_pstep hS2 hA2 (PStep.refl hT1.1.check.state)
  refine Sim.bindK (K := ibtsW.k_check_block_teles p (k + 1) (r2.headD 0)) (body := fun r3 m3 =>
      ibtsW.k_sl_cons p (callW p (k + 1) "sl_cons" [r2.headD 0, r3.headD 0, r3.tail.headD 0] m3)) rfl (fun _ _ => rfl)
    (ih (by omega) m2 a1 (o + 1) (l - 1) rest restP hC2 (hrest.grow hg2) hA2
      (ConRon.Bridge.Inductives.dMember_ext.list c1.ext _ _ hrestP)
      (ConRon.Bridge.denoteFEnv_mono c1.ext hfe)) ?_
  rintro r3 xs m3 a3 ⟨hC3, hg3, hxs, hA3, c3⟩
  refine Sim.mstep (K := ibtsW.k_sl_cons p) rfl (fun _ _ => rfl) fun r4 m4 h4 => ?_
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons (k + 1) _ _ _ _) h4
  obtain ⟨hS4, hg4, hd4, htop4⟩ := partsConsPL decTele_mono hW hC3.stage hxs.2 hxs.1
    (hd2.grow (decTele_mono _) hg3)
  have hA4 := consW_afr hW hA3
  exact Sim.ret ⟨hC3.of_pstep hS4 hA4 (PStep.refl hC3.check.state), (hg2.trans hg3).trans hg4,
    ⟨hd4, Nat.le_of_eq htop4⟩, hA4, c1.trans c3⟩

include hq henv hV hApd hCrk in
/-- **`check_block_teles` refines `checkBlockTeles`** under `StageC` (the members' denotations as
con-ron's `checkBlockTeles_specF` asks): the checked formers a slice of `[cvTa, s]` records,
decoded below the tops. -/
@[refines ConRon.Arena.checkBlockTeles]
theorem checkBlockTeles_refinesC (hP : InstProg p) (n : Nat) (hn : n ≤ 2 ^ 62) (s₀ : St)
    (a₀ : AState) (nP o l : Word)
    (mss : List MemberShape) (hC : StageC dn vis fe env s₀.mem a₀) (hms : MemsOK s₀.mem o l mss)
    (hA : AbsOK s₀.mem) {mssP : List ConLeche.MemberShape}
    (hmssP : mss.mapM (ConRon.Bridge.Inductives.dMember a₀.store) = some mssP)
    (hfe : ConRon.Bridge.denoteFEnv a₀.store fe = some env) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "check_block_teles" [vis, nP, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀ ∧
      StageC dn vis fe env s'.mem (AM.st (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      PSlR decTele (AM.res (ConRon.Arena.checkBlockTeles V fe nP.toNat mss) a₀) (r.headD 0)
        (r.tail.headD 0) s'.mem ∧ AbsOK s'.mem; ⊤⦄ :=
  triple_post (ibts_spec p hP.bTeles n s₀ vis nP o l) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hC', hg, hd, hA', _⟩ := Sim.run (ibtsW_simC hq henv hV hApd hCrk hP nP n hn _ a₀ o l mss mssP hC hms hA
      hmssP hfe) hm
    ⟨hl, hok, hC', hg, hd, hA'⟩

end sims

end L.Ind
