module

public import ConAgua.Arena.IndT.TailStream
public import ConAgua.Arena.IndT.PosMc
public import ConAgua.Arena.IndT.BlockC
import ConAgua.Arena.IndRealSctC
import ConAgua.Arena.RecCheckSpec.BlockNestedBit
import ConAgua.Arena.IndInstallSpec.ConsBlockCtors
import ConAgua.Arena.IndInstallSpec.InstallRec2PSl
import ConAgua.Arena.IndInstallSpec.PosFreeMfr
import ConAgua.Arena.IndInstallSpec.ConsRecsTFSimOf
import ConAgua.Arena.RefWalk
import ConAgua.Arena.IndT.GenRec1
import ConAgua.Arena.IndT.PassCS
import ConAgua.Arena.RecCheckSpec.EraseFVarTys
import all ConRon.Bridge.Inductives.BlockTail
import all ConAgua.Arena.IndInstall
import ConAgua.L.WordOff

@[expose] public section

/-!
# `check_block_tail`'s contract (lane `ronsync2`, stage 3)

`tail_ref`: `check_block_tail`'s unified model `ictlE` (`IndT/Tail`) refines `checkBlockTail`,
both outcomes, from `check_block_pass`'s out (con-ron's `checkBlockTail_of` for the twin side):
the index sorts (`iis_ref` through the call), the members' constructors (`mctorsW_dec`) consed
(`consBlockCtors_refines`; con-ron's `consBlockCtors_spec`), the flush (`ReadOK.flush`), the
nested bit, the recursor stage (`icr_ref` through the call; con-ron's `genRecCheck_spec` on the
twin's run), the stream half (`TsRefS`), the tables (`ctb_ref` through the call).
`tailRefS_of`: the contract `TailRefS` through the call, the walk memos outside the recursor
stage's (`maMR`, `mcMR`) kept across the whole call.
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **`checkBlockTail` at `check_block_tail`'s calls, the `let`s inlined.** -/
theorem checkBlockTail_split' (mode : ConLeche.CheckMode) (block : List IConstantInfo) (q : BlockPass) :
    ConRon.Arena.checkBlockTail mode block q =
      (ConRon.Arena.checkBlockIdxSorts mode q.env1 q.p q.p.members >>= fun _ =>
        ConRon.Arena.flushCaches >>= fun _ =>
        ConRon.Arena.checkBlockRec mode (ConRon.Arena.consBlockCtors q.p.nP q.p.memberCtors q.env1) q.p
            (ConRon.Arena.blockNestedBit q.p q.kinds) q.params q.tbl q.rd q.cls block >>= fun x =>
        tailStreamT mode q.p x.1 x.2 >>= fun fe₃ =>
        ConRon.Arena.checkBlockTables q.p fe₃ q.p.members >>= fun _ => pure fe₃) := by
  rw [checkBlockTail_split]

/-- What `check_block_tail`'s model gives (from `m`, `a`): the stage at the returned view, the
pools grown, `AbsOK`, the recursor stage's memos, the twin's step. -/
structure TailPostM (m : Mem) (a : AState) (w : Word) (fe' : IFEnv) (m' : Mem) (a' : AState) : Prop where
  stage : StageR w fe' m' a'
  grow : IWGrow m m'
  abs : AbsOK m'
  rc : RcMR m'
  inst : ConRon.Bridge.Inductives.InstStep a a'

/-- The callees of `check_block_tail` before the recursor stage, which keep the recursor stage's
memos and the `MAM` memo. -/
def tailPreCallees : List FnName :=
  ["check_block_idx_sorts", "block_shape_member_ctors", "cons_block_ctors", "flush_caches"]

section sims
variable {p : Prog} (hkp : KnotStageProg p) (hV : CcvProg p) (hApd : ApdF p) (hCrk : CrKeep p)
  (hCrf : CrfF p) (hIlpf : IlpfF p) (hOpf : OpfF p) (hLC : LvlCacheProg p)
  (hLT : p.lookup "lv_leq_top" = some lvLeqTop)

include hkp hV hApd hCrk hCrf hIlpf hOpf hLC hLT in
/-- **`check_block_tail`'s model refines `checkBlockTail`, both outcomes.** -/
theorem tail_ref (hP : TailProg p) (hMc : McLook p) (P : GrcProgE p) (hF : FtProg p)
    (hWt : WhnfTopE p) {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    (hfR : ∀ f ∈ grcMemoCallees, RcKeepF p f) (hfRc : ∀ f ∈ grcRcCallees, RcKeepF p f)
    (hMa : ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"], MaKeepF p f)
    (hOwn : OwnKeepF p "class_recs_rules_ok") (hkeep : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hRk : ∀ f ∈ tailPreCallees, RcKeepF p f) (hMk : ∀ f ∈ tailPreCallees, MaKeepF p f)
    (hts : TsRefS (VerdictCtxU p) p dn) (N : Nat) (hN : N ≤ 2 ^ 62 + 1)
    {vis : Word} {env₁ : ConLeche.Env} {m : Mem} {a : AState} {bO bL w : Word}
    {block : List IConstantInfo} {blockP : List ConLeche.ConstantInfo} {q : BlockPass}
    {qP : ConLeche.BlockPass ConLeche.Env}
    (hB : BkSt dn vis q.env1 env₁ m a) (hq : BPassR vis q.env1 m w q)
    (hsl : ShapeSl m (rdW (m.arr64 IW) (w + 1)))
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block)
    (hbP : Frontend.denoteCIList a.store block = some blockP)
    (hrel : ConRon.Bridge.Inductives.EnvRel env₁ q.env1 a.store) (henv₁ : ConLeche.EnvWF env₁)
    (hqP : ConRon.Bridge.Inductives.dPass a.store env₁ q = some qP)
    (hT : ∀ cv ∈ qP.p.formers, ConLeche.Expr.WScoped 0 cv.type)
    (henv₂ : ConLeche.EnvWF (ConLeche.consBlockCtors qP.p.nP qP.p.memberCtors env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M) (hpl : qP.params.length = qP.p.nP)
    (hnPb : q.p.nP + 1 < 2 ^ 64) :
    RefE (VerdictCtxU p) (ictlE p N m bO bL w) (ConRon.Arena.checkBlockTail V block q) a
      (fun v x a' => TailPostM m a v.1 x v.2 a') := by
  obtain ⟨fe, bs, kinds, params, rd, cls, tbl⟩ := q
  obtain ⟨hdq, hBB, hw0, hsrc⟩ := hq
  dsimp only at hB hdq hw0 hsrc hrel hnPb ⊢
  have hC := hB.c
  have hS := hC.stage
  have hA := hB.abs
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have e : ∀ k : Nat, k < 11 → ∀ x : Word, x = w + UInt64.ofNat k → x.toNat = w.toNat + k :=
    fun k hk x hx => by rw [hx]; exact L.toNat_add_ofNat_of_lt _ _ (by have := hBB.1; omega)
  -- the record
  have hdq' : decBPass fe (truncM m) w.toNat = some ⟨fe, bs, kinds, params, rd, cls, tbl⟩ := hdq
  simp only [decBPass, bind, Option.bind_eq_some_iff, pure, Option.some.injEq, BlockPass.mk.injEq,
    true_and] at hdq'
  obtain ⟨pw, hpw, bs, hbs0, kinds, hkd, params, hpar0, rdp, hrdp, rd, hrd0, cls, hcls0, tbl, htbl0, rfl, rfl, rfl, rfl, rfl,
    rfl⟩ := hdq'
  -- con-ron's reading of the pass record
  obtain ⟨-, hpP, -, hpaP, hrdP, hclP, htbP⟩ := ConRon.Bridge.Inductives.dPass_inv hqP
  obtain ⟨hmsP, -, hnPP, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hpP
  have hWm : ∀ ms ∈ qP.p.members, ConLeche.Expr.WScoped 0 ms.cvT.type :=
    fun ms hms => hT ms.cvT (List.mem_map_of_mem hms)
  -- the record's words
  have r : ∀ m', IWGrow m m' → ∀ k, k < 11 → ∀ x : Word, x = w + UInt64.ofNat k →
      rdW (m'.arr64 IW) x = rdW (m.arr64 IW) x :=
    fun m' hg k hk x hx => rdW_iw_grow hg (by rw [e k hk x hx]; have := hBB.1; omega)
  obtain ⟨hw1, hpwb⟩ := bpWord hpw (e 1 (by decide) (w + 1) rfl)
  have hkfm : ∀ q, OMono (fun m => decLH m (decPL m (decLH m (decKL m))) q) :=
    fun q => OMono.decAt (fun o l => OMono.decPL (fun q => OMono.decAt (fun o l => decKL_mono o l) q) o l) q
  have hks := bpPSl hkfm hkd (hBB.2 2 (by simp)) (w := w + 2) (w1 := w + 3)
    (e 2 (by decide) _ rfl) (e 3 (by decide) _ rfl)
  obtain ⟨hpd, hpb⟩ := bpHSl hpar0 (hBB.2 4 (by simp)) (w := w + 4) (w1 := w + 5)
    (e 4 (by decide) _ rfl) (e 5 (by decide) _ rfl)
  obtain ⟨hw6, hrdb⟩ := bpWord hrdp (e 6 (by decide) _ rfl)
  have hrdD : DecB (fun m' => decCR m' (rdW (m.arr64 IW) (w + 6)).toNat) m rd := by
    show decCR (truncM m) (rdW (m.arr64 IW) (w + UInt64.ofNat 6)).toNat = some rd
    rw [hw6, UInt64.toNat_ofNat_of_lt' hrdb]; exact hrd0
  have hcls' := bpPSl (fun q => decTM_mono q) hcls0 (hBB.2 7 (by simp)) (w := w + 7) (w1 := w + 8)
    (e 7 (by decide) _ rfl) (e 8 (by decide) _ rfl)
  have htbl' := bpPSl (fun q => decNCN_mono q) htbl0 (hBB.2 9 (by simp)) (w := w + 9) (w1 := w + 10)
    (e 9 (by decide) _ rfl) (e 10 (by decide) _ rfl)
  -- `check_block_idx_sorts`
  rcases N with _ | n
  · rw [ictlE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  have hn : n ≤ 2 ^ 62 := by omega
  rw [ictlE.arm1, hw0, checkBlockTail_split']
  dsimp only
  generalize hpp : rdW (m.arr64 IW) (w + 1) = pp at hsl hsrc hw1 ⊢
  have hbsD : DecB (fun m => decBS m pp.toNat) m bs := by
    show decBS (truncM m) pp.toNat = some bs
    rw [hw1, UInt64.toNat_ofNat_of_lt' hpwb]; exact hbs0
  obtain ⟨-, hq9, hmv⟩ := partsShapeFacts hbsD hsrc
  obtain ⟨hmd0, hmb0, -, -⟩ := bsAt hbsD hsl
  have hR0 : RcMR m := ⟨hB.ind.stage.pos, hB.ind.stage.ta⟩
  refine RefE.bindRun (s₀ := ⟨m, Locals.init []⟩) (fun _ => ictlE.k_check_block_idx_sorts.none ..)
    (iisE_spec p hP.idx hOpf n _ _ _ _ _) (fun hG => hG.nv) (fun hG => hG.toVerdictCtx)
    (iis_ref hkp henv₁ hLC hLT hP.idx pp bs n hn hC hA hbsD hsrc ⟨hmd0, hmb0⟩ hpP hmsP hWm)
    fun r1 s1 _ a1 c1 _ _ hI1 => ?_
  rw [ictlE.k_check_block_idx_sorts.arm1]
  have d1 := callW_of_callE c1
  have hC1 := hI1.stage
  have hg1 := hI1.grow
  have hA1 := hI1.abs
  have c1' := hI1.core
  dsimp only at hC1 hg1 hA1 c1'
  have hR1 : RcMR s1.mem := hRk _ (by simp [tailPreCallees]) _ _ _ _ _ d1 hR0
  have hma1 := hMk _ (by simp [tailPreCallees]) _ _ _ _ _ d1 hB.ind.stage.ma
  -- `block_shape_member_ctors` (L only)
  have hq1 := hbsD.grow (decBS_mono _) hg1
  have hsl1 := hsl.grow' hbsD hg1
  refine RefE.onlySim (fun _ => ictlE.k_block_shape_member_ctors.none ..)
    (Q := fun r m2 => callW p n "block_shape_member_ctors" [pp] s1.mem = some (r, m2))
    (fun _ _ h => h) fun r2 m2 c2 => ?_
  obtain ⟨s2, hs2, -, hW2⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (blockShapeMemberCtors_spec p hMc.ha hMc.hc hMc.hp n _ pp) c2
  subst hs2
  obtain ⟨hr2, hcss2, hg2, hfr2, hroom2⟩ := mctorsW_dec hW2 hC1.stage.iw.iwSize hC1.stage.iw.ctl
    (ShapeSl.membersB hq1 hsl1) hsl1
  rw [ictlE.k_block_shape_member_ctors.arm1, hr2]
  simp only [List.headD_cons, List.tail_cons]
  generalize rdW (s1.mem.arr64 CTL) 200 = caO at hcss2 ⊢
  generalize (UInt64.ofNat bs.k : Word) = caL at hcss2 ⊢
  have hS2 : StageR vis fe s2.mem a1 := stage_frame_iw hC1.stage hfr2 hroom2
  have hA2 : AbsOK s2.mem := AFr.of_frame hfr2 (by decide) (by decide) hA1
  have hR2 := hRk _ (by simp [tailPreCallees]) _ _ _ _ _ c2 hR1
  have hma2 := hMk _ (by simp [tailPreCallees]) _ _ _ _ _ c2 hma1
  have g12 := hg1.trans hg2
  -- `cons_block_ctors` (the twin's `fe₂`, a pure function)
  have h4 : (rdW (s2.mem.arr64 IW) (pp + 4)).toNat = bs.nP :=
    (bsAt (hbsD.grow (decBS_mono _) g12) (hsl.grow' hbsD g12)).2.2.2
  have hcssN : PSlR decCNS bs.memberCtors caO caL s2.mem :=
    ⟨decPL_weak (fun _ _ h => decCNSB_decCNS (m := s2.mem) h) hcss2.dec, hcss2.bound⟩
  refine RefE.onlySim (fun _ => ictlE.k_cons_block_ctors.none ..)
    (Q := fun r m3 => callW p n "cons_block_ctors" [rdW (s2.mem.arr64 IW) (pp + 4), caO, caL, vis] s2.mem
      = some (r, m3)) (fun _ _ h => h) fun r3 m3 c3 => ?_
  obtain ⟨s3, hs3, -, hS3, hg3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (consBlockCtors_refines p hP.recp hP.hci hP.hcs hP.hcbc n _ a1 dn fe _ _ _ vis bs.memberCtors hS2 hcssN) c3
  subst hs3
  rw [h4] at hS3
  rw [ictlE.k_cons_block_ctors.arm1]
  have hA3 : AbsOK s3.mem := hkeep _ (by simp [tailKeepCalleesC]) _ _ _ _ _ c3 hA2
  have hR3 := hRk _ (by simp [tailPreCallees]) _ _ _ _ _ c3 hR2
  have hma3 := hMk _ (by simp [tailPreCallees]) _ _ _ _ _ c3 hma2
  obtain ⟨env₂, hrel₂, he₂⟩ := (ConRon.Bridge.Inductives.consBlockCtors_spec c1'.ok.state.wf bs.nP
    bs.memberCtors qP.p.memberCtors fe env₁
    (ConRon.Bridge.Inductives.memberCtors_denote (ConRon.Bridge.Inductives.dShape_ext c1'.ext _ _ hpP))
    (hrel.mono c1'.ext)).denote
  have henv₂' : ConLeche.EnvWF env₂ := by rw [he₂, hnPP]; exact henv₂
  -- the flush
  refine RefE.bindSim (fun _ => ictlE.k_flush_caches.none ..) (flushSimT hP.flush n hS3 hA3)
    fun r4 _ m4 a4 c4 hrun4 ⟨_, hS4, hg4, hA4, _⟩ => ?_
  rw [ictlE.k_flush_caches.arm1]
  obtain ⟨hck4, i4, hst4⟩ := ConRon.Bridge.Inductives.ReadOK.flush
    (⟨c1'.ok.state, c1'.ok.pins, hrel₂.ifenv⟩ : ConRon.Bridge.Inductives.ReadOK env₂ _ a1) hrun4
  have x04 : ConRon.Arena.Ext a.store a4.store := by rw [hst4]; exact c1'.ext
  have hC4 := StageC.of_checkE hC hS4 hA4 hck4 x04
  have hR4 := hRk _ (by simp [tailPreCallees]) _ _ _ _ _ c4 hR3
  have hma4 := hMk _ (by simp [tailPreCallees]) _ _ _ _ _ c4 hma3
  have g04 := (g12.trans hg3).trans hg4
  -- `block_nested_bit` (the twin's `nested`, a pure function)
  rw [r _ g04 2 (by decide) (w + 2) rfl, r _ g04 3 (by decide) (w + 3) rfl]
  have hbs4 := hbsD.grow (decBS_mono _) g04
  have hks4 := hks.grow hkfm g04
  refine RefE.onlySim (fun _ => ictlE.k_block_nested_bit.none ..)
    (Q := fun r m5 => callW p n "block_nested_bit" [pp, rdW (m.arr64 IW) (w + 2), rdW (m.arr64 IW) (w + 3)] m4
      = some (r, m5)) (fun _ _ h => h) fun r5 m5 c5 => ?_
  obtain ⟨s5, hs5, hs5', hr5⟩ := triple_of_callW (s₀ := ⟨m4, Locals.init []⟩)
    (blockNestedBit_refines p hP.nf hP.ni hP.nm hP.nk hP.ng hP.nb n _ _ _ _ bs kinds hS4.iw.iwSize
      (DecB.get (decBS_mono _) hbs4) (DecB.get (OMono.decPL hkfm _ _) hks4.dec)) c5
  subst hs5'
  subst hs5
  have hnb : (r5.headD 0 != 0) = ConRon.Arena.blockNestedBit bs kinds := by
    rw [hr5]; cases ConRon.Arena.blockNestedBit bs kinds <;> rfl
  rw [ictlE.k_block_nested_bit.arm1]
  -- `check_block_rec`
  rw [r _ g04 4 (by decide) (w + 4) rfl, r _ g04 5 (by decide) (w + 5) rfl, r _ g04 6 (by decide) (w + 6) rfl,
    r _ g04 7 (by decide) (w + 7) rfl, r _ g04 8 (by decide) (w + 8) rfl, r _ g04 9 (by decide) (w + 9) rfl,
    r _ g04 10 (by decide) (w + 10) rfl]
  have hsl4 := hsl.grow' hbsD g04
  have hBS4 : BSOK m4 pp.toNat bs := by
    obtain ⟨-, -, hmv4⟩ := partsShapeFacts hbs4 hsl4.1
    exact ⟨hbs4, hsl4.1, fun o l j v ho hl hj hv => by have := hmv4 o l j v ho hl hj hv; omega⟩
  have dd1 := ConRon.Bridge.Inductives.dShape_ext x04 _ _ hpP
  have dd2 := ConRon.Bridge.denoteEList_ext x04 _ _ hpaP
  have dd3 := ConRon.Bridge.Inductives.dCtorNf_ext.list x04 _ _ htbP
  have dd4 := ConRon.Bridge.Inductives.dClassRead_ext x04 _ _ hrdP
  have dd5 := ConRon.Bridge.Inductives.dMajor_ext.list x04 _ _ hclP
  have dd6 := ConRon.Bridge.denoteCIList_mono x04 _ _ hbP
  have hR6 := icr_ref hkp henv₂' hV hApd hCrk hCrf hIlpf P hF hWt hfR hCs hMa hOwn
    (fun f hf => hkeep f (List.mem_append_right _ hf)) hfRc n hn hC4 hBS4 hsl4.2.1
    (by rw [decHL_grow3 g04 hpb]; exact hpd) (Nat.le_trans hpb g04.iw) (htbl'.grow (fun q => decNCN_mono q) g04)
    (hrdD.grow (decCR_mono _) g04) (hcls'.grow (fun q => decTM_mono q) g04)
    (hblk.grow (decEBlk_mono _ _ _) g04) hR4 hA4 hma4 hrel₂.gate dd1 dd2 dd3 dd4 dd5 dd6 hT hMs
    (nested := r5.headD 0)
  rw [hnb] at hR6
  refine RefE.bindRunLe (n' := n + 2) (by omega) (fun _ => ictlE.k_check_block_rec.none ..)
    (icrE_spec p P hP.crec (n + 2) ⟨m4, Locals.init []⟩ _ _ _ _ _ _ _ _ _ _ _ _) (fun hG => hG.nv) id hR6
    fun r6 s6 y a6 _ _ hrun6 hG6 => ?_
  dsimp only at hG6
  obtain ⟨c6', outP, ⟨hout, -, hfeq⟩, hGRF⟩ := ConRon.Bridge.Inductives.genRecCheck_spec _
    ConRon.Bridge.CoreSpec.of_core henv₂' hrel₂.gate bs qP.p _ params qP.params tbl qP.tbl.toList rd qP.rd
    cls qP.cls block blockP hMs hT a4 a6 y hck4 ⟨dd1, dd2, dd3, dd4, dd5, dd6⟩ hrun6
  have henvG : ConLeche.EnvWF (ConLeche.consBlockRecsT qP.p 0 outP env₂) := by
    obtain ⟨FR, hFR⟩ := hGRF
    rw [ConLeche.genRecCheck_datF] at hFR
    exact ConLeche.Cached.genRecCheck_recsWF henv₂' hFR hpl (fun M hM => (hMs M hM).2.1)
  have x16 : ConRon.Arena.Ext a1.store a6.store := by rw [← hst4]; exact c6'.ext
  have hrel₂b := ConRon.Bridge.Inductives.BT.EnvRel.feq hfeq (hrel₂.mono x16)
  -- `check_block_tail_stream`
  rw [ictlE.k_check_block_rec.arm1]
  have g06 := g04.trans hG6.grow
  have x06 : ConRon.Arena.Ext a.store a6.store := x04.trans c6'.ext
  have hp36 : pp.toNat + 3 < iwTop s6.mem := by have := Nat.le_trans hq9 g06.iw; omega
  refine RefE.bindE (fun _ => ictlE.k_check_block_tail_stream.none ..) id
    (hts n hn (r6.headD 0) y.1 env₂ s6.mem a6 pp (r6.tail.headD 0) (r6.tail.tail.headD 0) bs qP.p y.2 outP
      hG6.stage hG6.abs hG6.rc hrel₂b henvG (hbsD.grow (decBS_mono _) g06) (hsl.grow' hbsD g06).2.1 hp36
      ⟨hG6.rrs.1, hG6.rrs.2⟩ (ConRon.Bridge.Inductives.dShape_ext x06 _ _ hpP) hout)
    fun ⟨r7, m7⟩ fe₃ a7 _ hT7 => ?_
  rw [ictlE.k_check_block_tail_stream.arm1]
  dsimp only at hT7 ⊢
  -- `check_block_tables`
  have g07 := g06.trans hT7.grow
  have hbs7 := hbsD.grow (decBS_mono _) g07
  obtain ⟨hmd7, hmb7, -, -⟩ := bsAt hbs7 (hsl.grow' hbsD g07)
  have x07 : ConRon.Arena.Ext a.store a7.store := x06.trans hT7.inst.ext
  refine RefE.bindRun (s₀ := ⟨m7, Locals.init []⟩) (fun _ => ictlE.k_check_block_tables.none ..)
    (ctbE_spec p hP.tabs n _ pp (r7.headD 0) _ _) (fun hG => hG.nv) (fun _ => trivial)
    (ctb_ref hP.tabs hApd pp (r7.headD 0) fe₃ bs hnPb n m7 a7 _ _ bs.members hT7.stage.stage hbs7
      ⟨hmd7, hmb7⟩ hT7.abs hT7.stage.check.state
      ⟨_, denoteNList_mapM (ConRon.Bridge.Inductives.BlockShape.lps_spec (ConRon.Bridge.Inductives.dShape_ext x07 _ _ hpP))⟩
      ⟨_, ConRon.Bridge.Inductives.dMember_ext.list x07 _ _ hmsP⟩)
    fun r8 s8 _ a8 _ _ _ hTb => ?_
  rw [ictlE.k_check_block_tables.arm1]
  exact RefE.ret rfl ⟨hTb.stage, g07.trans hTb.grow, hTb.abs, hT7.rc.fr hTb.frame,
    (c1'.toInst.trans i4).trans (c6'.toInst.trans (hT7.inst.trans hTb.step.toInst))⟩

include hkp hV hApd hCrk hCrf hIlpf hOpf hLC hLT in
/-- **`check_block_tail`'s contract** (`TailRefS`): `tail_ref` through the call; the walk memos
outside the recursor stage's (`maMR`, `mcMR`) kept across the whole call, the core's memos from
`AbsOK`. -/
theorem tailRefS_of (hP : TailProg p) (hMc : McLook p) (P : GrcProgE p) (hF : FtProg p)
    (hWt : WhnfTopE p) {dn : NIdx → Option ConLeche.Name} (hCs : CcvSims p dn)
    (hfR : ∀ f ∈ grcMemoCallees, RcKeepF p f) (hfRc : ∀ f ∈ grcRcCallees, RcKeepF p f)
    (hMa : ∀ f ∈ ["gen_rec_check_prep", "class_fe_r", "block_shape_names_of", "flush_caches"], MaKeepF p f)
    (hOwn : OwnKeepF p "class_recs_rules_ok") (hkeep : ∀ f ∈ tailKeepCalleesC, AbsKeep p f)
    (hRk : ∀ f ∈ tailPreCallees, RcKeepF p f) (hMk : ∀ f ∈ tailPreCallees, MaKeepF p f)
    (hts : TsRefS (VerdictCtxU p) p dn) (hMaT : MaKeepF p "check_block_tail")
    (hMcT : ∀ (n : Nat) (vs : List Word) (m : Mem) (r : List Word) (m' : Mem),
      callW p n "check_block_tail" vs m = some (r, m') → (∃ mp, mcMR m mp) → ∃ mp, mcMR m' mp) :
    TailRefS (VerdictCtxU p) p dn := by
  intro n hn vis env₁ m a bO bL w block blockP q qP hB hq hsl hblk _ hbP _ hrel henv₁ hqP hT henv₂ hMs hpl hnPb
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (G := VerdictCtxU p) (ictlE_spec p hP n _ bO bL w)
    (fun (hG : VerdictCtxU p) => hG.nv)
    (tail_ref hkp hV hApd hCrk hCrf hIlpf hOpf hLC hLT hP hMc P hF hWt hCs hfR hfRc hMa hOwn hkeep hRk hMk hts n
      (by omega) hB hq hsl hblk hbP hrel henv₁ hqP hT henv₂ hMs hpl hnPb)
  refine RefE.callOk h fun ⟨r, m'⟩ x a' hc hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  have d := callW_of_callE hc
  exact ⟨hR.stage, ⟨⟨⟨hR.rc.pos, hMaT _ _ _ _ _ d hB.ind.stage.ma, hMcT _ _ _ _ _ d hB.ind.stage.mc, hR.rc.ta⟩,
    hR.abs.i1, hR.abs.cr⟩, hR.abs.coreMemos, hR.abs⟩, hR.grow, hR.inst⟩

end sims

end L.Ind

end
