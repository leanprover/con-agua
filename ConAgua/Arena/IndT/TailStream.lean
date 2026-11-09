module

public import ConAgua.Arena.IndT.Tail
public import ConAgua.Arena.GrindAttr
public import ConAgua.L.GrindAttr
import ConAgua.L.ModelGen
import ConAgua.Checker.NoVerdictTree
import all ConAgua.Arena.IndInstall
import all ConAgua.Arena.IndStream
import ConAgua.Arena.IndSumSpec.ConsBlockRecsTF
import ConAgua.Arena.IndPartsSpec.BlockRecLpsOk
import ConAgua.Arena.IndPartsSpec.RulePrefixAt
import ConAgua.Arena.IndDecStab
import ConAgua.Arena.RecClassSpec.MjProg
import ConAgua.Arena.RefWalk
public import ConAgua.Arena.IndT.RecsTemp
import ConAgua.Arena.RecGenSpec.FlushStage
import ConAgua.Arena.CoreRefine
import ConAgua.Arena.ScratchRefine
import ConAgua.Arena.IndT.GenRec1
import ConAgua.Arena.IndT.PassCS
import ConAgua.Arena.IndInstallSpec.PapW
import ConAgua.Arena.IndInstallSpec.IcvgW
public import ConAgua.Arena.IndT.IdxSorts
public import ConAgua.Arena.IndT.GenRec3
import all ConRon.Bridge.Inductives.BlockTail

@[expose] public section

/-!
# `check_block_tail_stream` and `stream_k_check`: the unified models (lane `ronsync2`, stage 3)

`check_block_tail_stream(p, fe2b, out.off, out.len)` (`IndInstall.lean`) is `tailStreamT`
(`IndT/Tail`): `stream_k_check` and `stream_recs_check` through their calls, `block_rec_infos_tf`,
`cons_block_recs_temp`, the flushes and `gen_rec_check_pop_all` (outside the verdict closure) lifted.
The refinements (`streamKCheck`, `streamRecsCheck` and its callees in `Arena/IndStream`) are still
to write (handoff in `_tmp/ronsync2/area-ind.md`).
-/

noncomputable section

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-- The lookups of the stream half's models. -/
structure TsLook (p : Prog) : Prop where
  ts : p.lookup "check_block_tail_stream" = some checkBlockTailStream
  skc : p.lookup "stream_k_check" = some streamKCheckL

set_option experimental.vcgen true in
/-- **`stream_k_check`'s unified model**: `rec_k_expected` lifted. -/
l_model skcE_spec (p : Prog) (hP : TsLook p)
  fns [hP.skc ↦ skcE]
  specs [callW_spec p n "rec_k_expected"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

set_option experimental.vcgen true in
/-- **`check_block_tail_stream`'s unified model**: the K flags and the stream's recursors through
their calls, the rest lifted. -/
l_model ctsE_spec (p : Prog) (hP : TsLook p)
  fns [hP.ts ↦ ctsE]
  specs [callW_spec p n "block_rec_infos_tf", callW_spec p n "cons_block_recs_temp",
    callW_spec p n "flush_caches", callW_spec p n "gen_rec_check_pop_all"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_idxGE, evalE_tagE] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-! ## `stream_k_check` -/

/-- A flag word of a record decoded below the top, read. -/
theorem iwB_trunc_rd {m : Mem} {w : Word} {k : Nat} {b : Bool}
    (h : iwB (truncM m) (w.toNat + k) = some b) : (rdW (m.arr64 IW) (w + UInt64.ofNat k) != 0) = b := by
  simp only [iwB, bool?, Option.map_eq_some_iff] at h
  obtain ⟨v, hv, rfl⟩ := h
  obtain ⟨hlt, hv'⟩ := truncM_iw_get hv
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hi : w.toNat + k < 2 ^ 64 := by omega
  have := iwB_rdW (m := m) (i := w.toNat + k) (b := v != 0) (by simp [iwB, bool?, hv']) hi
  have e : (UInt64.ofNat (w.toNat + k) : Word) = w + UInt64.ofNat k := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' hi, UInt64.toNat_ofNat_of_lt' (show k < 2 ^ 64 by omega)]
    omega
  rwa [e] at this

/-- `rec_k_expected` answers `0` or `1`. -/
theorem rkW_01 {m : Mem} {p M w : Word} (h : rkW m p M = some w) : w = 0 ∨ w = 1 := by
  unfold rkW at h
  split at h
  · exact .inl (Option.some.inj h).symm
  split at h
  · exact .inl (Option.some.inj h).symm
  obtain rfl := (Option.some.inj h).symm
  split <;> split <;> split <;> simp

/-- **`stream_k_check` refines `streamKCheck`, both outcomes**: the records' flags against
`rec_k_expected` (`rkW_ok`), the memory and the twin's state unchanged. -/
theorem skc_ref {p : Prog} (hL : CbrLook p) {G : Prop} (pp : Word) (bs : BlockShape) :
    ∀ (n : Nat) (m : Mem) (a : AState) (ro rl go gl : Word) (rcs : List RecShape)
      (gs : List (IConstantVal × TargetMajor × List EIdx)),
    DecB (fun m => decBS m pp.toNat) m bs → PSlR decRS rcs ro rl m → PSlR decRR gs go gl m →
    (m.arr64 IW).size < 2 ^ 64 →
    RefE G (skcE p n m pp ro rl go gl) (ConRon.Arena.streamKCheck bs rcs gs) a
      (fun v _ a' => a' = a ∧ v.2 = m) := by
  intro n
  induction n with
  | zero => intro m a ro rl go gl rcs gs _ _ _ _; rw [skcE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  | succ n ih =>
  intro m a ro rl go gl rcs gs hbs hr hg hsz
  by_cases hz : rl = 0 ∨ gl = 0
  · rw [skcE.arm1 _ _ _ _ _ _ _ _ hz]
    refine RefE.ret (y := ()) (a' := a) ?_ ⟨rfl, rfl⟩
    rcases hz with h0 | h0
    · have hlen : rcs.length = rl.toNat := decPL_length _ (show decPL (truncM m) _ _ _ = some rcs from hr.dec)
      rw [h0] at hlen
      obtain rfl : rcs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      cases gs <;> rfl
    · have hlen : gs.length = gl.toNat := decPL_length _ (show decPL (truncM m) _ _ _ = some gs from hg.dec)
      rw [h0] at hlen
      obtain rfl : gs = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
      cases rcs <;> rfl
  obtain ⟨hr0, hg0⟩ := not_or.mp hz
  obtain ⟨rc, rcs', rfl, hrc, hr'⟩ := PSlR.uncons hr hr0 hsz
  obtain ⟨g, gs', rfl, hgd, hg'⟩ := PSlR.uncons hg hg0 hsz
  rw [skcE.arm2 _ _ _ _ _ _ _ _ hz]
  -- the generated recursor's major
  have hgd0 : decRR (truncM m) (rdW (m.arr64 IW) go).toNat = some g := hgd
  obtain ⟨cv, M, rh⟩ := g
  simp only [decRR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hgd0
  obtain ⟨cvp, -, cv', -, mp, hmp, TM', hTM', rh', -, he⟩ := hgd0
  simp only [Prod.mk.injEq] at he
  obtain ⟨-, rfl, -⟩ := he
  obtain ⟨-, hmpm⟩ := rec2IwN_trunc hmp
  obtain ⟨e1, t1⟩ := rec2RdN (w := rdW (m.arr64 IW) go) (k := 1) hmpm hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl] at e1
  have hM : DecB (fun m => decTM m (UInt64.ofNat mp : Word).toNat) m TM' := by
    show decTM (truncM m) _ = some TM'; rw [t1]; exact hTM'
  obtain ⟨isK, hk, hkE⟩ := rkW_ok hbs hM hsz
  -- the record's flag
  have hrc0 : decRS (truncM m) (rdW (m.arr64 IW) ro).toNat = some rc := hrc
  have hK : (rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) != 0) = rc.isK :=
    iwB_trunc_rd (k := 6) (decRS_some hrc0).2.2.2.2.2
  rw [e1]
  refine RefE.onlySim (fun _ => skcE.k_rec_k_expected.none _ _ _ _ _ _ _ _ _)
    (Q := fun r m₁ => m₁ = m ∧ r.headD 0 = isK) (fun r m₁ hc => ?_) fun r m₁ ⟨hm₁, hr⟩ => ?_
  · obtain ⟨s', hs', -, hm', hrk⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (rk_spec p hL n ⟨m, Locals.init []⟩ pp (UInt64.ofNat mp)) hc
    rw [hk] at hrk
    exact ⟨hs' ▸ hm', (Option.some.inj hrk).symm⟩
  subst m₁
  have hcond : (rc.isK == ConRon.Arena.recKExpected bs TM') = true ↔
      ((if rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) ≠ 0 then (1 : Word) else 0) = r.headD 0) := by
    rw [← hK, ← hkE, hr]
    rcases rkW_01 hk with rfl | rfl <;>
      by_cases hX : rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) = 0 <;> simp [hX]
  by_cases hkk : (if rdW (m.arr64 IW) (rdW (m.arr64 IW) ro + 6) ≠ 0 then (1 : Word) else 0) = r.headD 0
  · rw [skcE.k_rec_k_expected.arm1 _ _ _ _ _ _ _ _ _ _ hkk]
    have hc' : (rc.isK == ConRon.Arena.recKExpected bs TM') = true := hcond.mpr hkk
    have htw : ConRon.Arena.streamKCheck bs (rc :: rcs') ((cv, TM', rh) :: gs') =
        ConRon.Arena.streamKCheck bs rcs' gs' := by
      simp only [ConRon.Arena.streamKCheck, hc']; rfl
    have IH := ih m a (ro + 1) (rl - 1) (go + 1) (gl - 1) rcs' gs' hbs hr' hg' hsz
    rw [htw]
    rcases hx : skcE p n m pp (ro + 1) (rl - 1) (go + 1) (gl - 1) with e | ⟨v, m2⟩
    · rw [skcE.k_stream_k_check.none]; rw [hx] at IH; exact IH
    · rw [skcE.k_stream_k_check.arm1]; rw [hx] at IH
      obtain ⟨y, a', hrun, rfl, hv⟩ := IH
      exact RefE.ret hrun ⟨rfl, hv⟩
  · rw [skcE.k_rec_k_expected.abort1 _ _ _ _ _ _ _ _ _ _ hkk]
    have hc' : (rc.isK == ConRon.Arena.recKExpected bs TM') = false := by
      exact Bool.eq_false_iff.mpr (mt hcond.mp hkk)
    intro _
    simp only [ConRon.Arena.streamKCheck, hc']
    exact ErrClaim.bind_left (ErrClaim.fail _ _ (by decide))

/-! ## `stream_recs_check`'s contract -/

local notation "V" => ConLeche.CheckMode.verified

/-- **`stream_recs_check(vis, recs.off, recs.len, gs.off, gs.len)`'s contract** (its refinement is
another worker's): `streamRecsCheck`, both outcomes, from the stage at the generated family's
environment, the stream's records and the generated ones decoded and denoted (con-ron's
`streamRecsCheck_spec`'s pre); the post `IisPost`'s (the stage, the pools grown, `AbsOK`, the
twin's core step). -/
def StreamRecsRefS (G : Prop) (p : Prog) (dn : NIdx → Option ConLeche.Name) : Prop :=
  ∀ (n : Nat), n ≤ 2 ^ 62 → ∀ (vis : Word) (fe : IFEnv) (env : ConLeche.Env) (m : Mem) (a : AState)
    (ro rl go gl : Word) (rcs : List RecShape) (gs : List (IConstantVal × TargetMajor × List EIdx))
    (rcsP : List ConLeche.RecShape)
    (gsP : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)),
    StageC dn vis fe env m a → AbsOK m → ConLeche.EnvWF env →
    PSlR decRS rcs ro rl m → PSlR decRR gs go gl m →
    rcs.mapM (ConRon.Bridge.Inductives.dRec a.store) = some rcsP →
    gs.mapM (ConRon.Bridge.Inductives.dRecOut a.store) = some gsP →
    RefE G (callE p n "stream_recs_check" [vis, ro, rl, go, gl] m)
      (ConRon.Arena.streamRecsCheck V fe rcs gs) a
      (fun rm _ a' => IisPost dn vis fe env m a rm.2 a')

/-- The stream's records, a slice below the top (`RecsB`). -/
theorem recsPSl {m : Mem} {pp : Word} {bs : BlockShape} (hbs : DecB (fun m => decBS m pp.toNat) m bs)
    (hrb : RecsB m pp) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    PSlR decRS bs.recs (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) m := by
  have hbs0 : decBS (truncM m) pp.toNat = some bs := hbs
  obtain ⟨-, hrecs, -⟩ := decBS_some hbs0
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hrecs
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨e2, t2⟩ := rec2RdN (w := pp) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := pp) (k := 3) (by simpa [Nat.add_assoc] using hlm) hsz
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  rw [e2, e3]
  exact ⟨by show decPL (truncM m) _ _ _ = _; rw [t2, t3]; exact hd,
    by rw [t2, t3]; exact hrb o l hom (by simpa [Nat.add_assoc] using hlm)⟩

/-- `flush_caches()` as a `Sim` keeping the stage, `AbsOK` and the own rows' counters. -/
theorem flushSimT {p : Prog} (hF : FlushProg p) (n : Nat) {vis : Word} {fe : IFEnv} {m : Mem}
    {a : AState} (hS : StageR vis fe m a) (hA : AbsOK m) :
    Sim (callW p n "flush_caches" [] m) ConRon.Arena.flushCaches a
      (fun _ _ m' a' => a' = { a with caches := Caches.empty } ∧ StageR vis fe m' a' ∧ IWGrow m m' ∧
        AbsOK m' ∧ ownC m' = ownC m) := by
  intro r m' hc
  obtain ⟨s', hs', -, hfok, hfm⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (flushCaches_spec p hF n _) hc
  subst hs'
  obtain ⟨hS', hg⟩ := flush_stage hS hfok
  refine ⟨(), _, flushCaches_run a, rfl, by rw [hfm]; exact hS', by rw [hfm]; exact hg,
    by rw [hfm]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA,
    by rw [hfm]; exact ownC_frame (flushMem_frame _) (by simp) (by decide)⟩

/-- The lookups of `check_block_tail_stream`'s callees. -/
structure TsProg (p : Prog) : Prop where
  look : TsLook p
  cbr : CbrLook p
  pu : p.lookup "erec_put" = some erecPut
  cbrt : CbrtLook p
  rs : p.lookup "env_row_set" = some envRowSetL
  push : p.lookup "env_push" = some envPushL
  rg : p.lookup "env_row_get" = some envRowGetL
  ia : p.lookup "iw_alloc" = some iwAlloc
  r3 : p.lookup "rec3" = some rec3
  cp : p.lookup "iw_copy" = some iwCopy
  sn : p.lookup "sl_snoc" = some slSnoc
  ept : p.lookup "env_pop_temp" = some envPopTempL
  gpa : p.lookup "gen_rec_check_pop_all" = some genRecCheckPopAll
  flush : FlushProg p

/-- **`check_block_tail_stream` refines `tailStreamT`, both outcomes** (con-ron's `checkBlockTail_of`
from "the K flags" to "the flush leaving them"): `stream_k_check` (`skc_ref`), the generated family's
records (`blockRecInfosTF_refines`), pushed in place (`cbrt_call`; con-ron's `consBlockRecsTemp_ok`),
a flush, the stream's recursors (the contract), the pops (`genRecCheckPopAll_refines`; con-ron's
`consBlockRecsTemp_pop`), a flush. -/
theorem ts_ref {p : Prog} {dn : NIdx → Option ConLeche.Name} {G : Prop} (hG : G → closedNV p _root_.L.Checker.nvFns = true)
    (P : TsProg p) (hsr : StreamRecsRefS G p dn)
    (hRc : ∀ f ∈ ["block_rec_infos_tf", "cons_block_recs_temp", "flush_caches", "stream_recs_check",
      "gen_rec_check_pop_all"], RcKeepF p f)
    (hAk : AbsKeep p "cons_block_recs_temp") (hAp : AbsKeep p "gen_rec_check_pop_all")
    (hOwn : OwnKeepF p "stream_recs_check") (n : Nat) (hn : n ≤ 2 ^ 62 + 1)
    {vis : Word} {fe : IFEnv} {env₂ : ConLeche.Env} {m : Mem} {a : AState} {pp go gl : Word}
    {bs : BlockShape} {bsP : ConLeche.BlockShape} {gs : List (IConstantVal × TargetMajor × List EIdx)}
    {gsP : List (ConLeche.ConstantVal × ConLeche.TargetMajor × List ConLeche.Expr)}
    (hC : StageC dn vis fe env₂ m a) (hA : AbsOK m) (hR : RcMR m)
    (hrel : ConRon.Bridge.Inductives.EnvRel env₂ fe a.store)
    (henvG : ConLeche.EnvWF (ConLeche.consBlockRecsT bsP 0 gsP env₂))
    (hbs : DecB (fun m => decBS m pp.toNat) m bs) (hrb : RecsB m pp) (hp3 : pp.toNat + 3 < iwTop m)
    (hgs : PSlR decRR gs go gl m) (hsh : ConRon.Bridge.Inductives.dShape a.store bs = some bsP)
    (hgP : gs.mapM (ConRon.Bridge.Inductives.dRecOut a.store) = some gsP) :
    RefE G (ctsE p n m pp vis go gl) (tailStreamT V bs fe gs) a
      (fun v fe' a' => TsPost dn env₂ m a v.1 fe' v.2 a') := by
  rcases n with _ | n
  · rw [ctsE.eq_1]; exact RefE.of_cls0 Err.cls_outOfFuel
  rw [ctsE.arm1]
  unfold tailStreamT
  have hsz := hC.stage.iw.iwSize
  have hrs := recsPSl hbs hrb hsz
  obtain ⟨-, hrecsP, -⟩ := ConRon.Bridge.Inductives.dShape_inv hsh
  -- `stream_k_check`
  refine RefE.bindE (fun _ => ctsE.k_stream_k_check.none ..) id
    (RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (G := G) (skcE_spec p P.look n _ pp _ _ go gl) hG
      (skc_ref P.cbr pp bs n m a _ _ go gl bs.recs gs hbs hrs hgs hsz)) fun ⟨r1, m1⟩ y a1 hrun1 ⟨s1, hs1, _, ha1, hm1⟩ => ?_
  simp only at hs1 hm1 ha1
  subst a1
  have em1 : m1 = m := by rw [← hs1]; exact hm1
  subst m1
  rw [ctsE.k_stream_k_check.arm1]
  have hsm : s1.mem = m := by simp_all
  rw [hsm]
  -- `block_rec_infos_tf`
  have hml : (0 : Word).toNat + gl.toNat < 2 ^ 64 := by simpa using gl.toNat_lt
  refine RefE.bindSim (fun _ => ctsE.k_block_rec_infos_tf.none ..)
    (Q := fun r infos m2 a2 => decPL m2 (decCI (erecP m2)) (r.headD 0).toNat (r.tail.headD 0).toNat = some infos ∧
      (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m2 ∧ StageR vis fe m2 a2 ∧ IWGrow m m2 ∧ AbsOK m2 ∧
      callW p n "block_rec_infos_tf" [pp, 0, go, gl] m = some (r, m2))
    (fun r m2 hc => by
      obtain ⟨s', hs', -, infos, a2, hrun, hd, hb, hS, hg, hA2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (blockRecInfosTF_refines p P.cbr P.pu n _ a fe vis pp 0 go gl bs gs hC.stage hbs hgs hml hA) hc
      subst hs'
      exact ⟨infos, a2, by simpa using hrun, hd, hb, hS, hg, hA2, hc⟩)
    fun r2 infos m2 a2 _ hrun2 ⟨hd2, hb2, hS2, hg2, hA2, c2⟩ => ?_
  rw [ctsE.k_block_rec_infos_tf.arm1]
  obtain ⟨p2, hinfos⟩ := ConRon.Bridge.Inductives.blockRecInfosTF_run bs bsP gs gsP 0 a a2 infos
    hC.check.state hsh hgP hrun2
  have hR2 : RcMR m2 := hRc _ (by simp) _ _ _ _ _ c2 hR
  -- `cons_block_recs_temp` (the twin's pure `consBlockRecsTemp`)
  refine RefE.onlySim (fun _ => ctsE.k_cons_block_recs_temp.none ..)
    (Q := fun r m3 => callW p n "cons_block_recs_temp" [r2.headD 0, r2.tail.headD 0, vis, 0, 0] m2 = some (r, m3))
    (fun r m3 hc => hc) fun r3 m3 c3 => ?_
  obtain ⟨hS3, hg3, hsp3, cs, hspc3, hPop3⟩ := cbrt_call P.cbrt P.rs P.push P.rg P.ia P.r3 P.cp P.sn c3 hS2 hd2 hb2
  have hA3 : AbsOK m3 := hAk _ _ _ _ _ c3 hA2
  have hR3 : RcMR m3 := hRc _ (by simp) _ _ _ _ _ c3 hR2
  rw [ctsE.k_cons_block_recs_temp.arm1]
  generalize hX : ConRon.Arena.consBlockRecsTemp infos fe [] = X at hS3 hsp3
  obtain ⟨news, hn, hpop⟩ := ConRon.Bridge.Inductives.BT.consBlockRecsTemp_pop infos fe []
  have hienvG := ConRon.Bridge.Inductives.BT.consBlockRecsTemp_ok p2.ok infos _ fe env₂ [] hinfos
    (hrel.mono p2.ext).ifenv hrel.gate hrel.stored
  rw [hX] at hn hpop hienvG
  rw [← ConRon.Bridge.Inductives.consBlockRecsT_eq] at hienvG
  obtain ⟨feG, prevs⟩ := X
  simp only [List.nil_append] at hn
  subst hn
  dsimp only at hS3 hsp3 hpop hienvG ⊢
  -- the flush entering it
  refine RefE.bindSim (fun _ => ctsE.k_flush_caches.none ..) (flushSimT P.flush n hS3 hA3)
    fun r4 _ m4 a4 c4 hrun4 ⟨ha4, hS4, hg4, hA4, hown4⟩ => ?_
  have hR4 : RcMR m4 := hRc _ (by simp) _ _ _ _ _ c4 hR3
  rw [ctsE.k_flush_caches.arm1]
  obtain ⟨hck4, i4, hst4⟩ := ConRon.Bridge.Inductives.ReadOK.flush
    (⟨p2.ok, hC.check.pins.mono p2.ext p2.pins, hienvG⟩ : ConRon.Bridge.Inductives.ReadOK _ _ a2) hrun4
  have hx4 : ConRon.Arena.Ext a.store a4.store := by rw [hst4]; exact p2.ext
  have hg04 := (hg2.trans hg3).trans hg4
  have hC4 : StageC dn (r3.headD 0) feG _ m4 a4 := StageC.of_checkE hC hS4 hA4 hck4 hx4
  -- the stream's recursors
  have hbs4 := hbs.grow (decBS_mono _) hg04
  have hrb4 := hrb.grow hg04 hp3
  refine RefE.bindE (fun _ => ctsE.k_stream_recs_check.none ..) id
    (RefE.callOk (hsr n (by omega) (r3.headD 0) feG _ m4 a4 _ _ go gl bs.recs gs bsP.recs gsP hC4 hA4 henvG
      (recsPSl hbs4 hrb4 hS4.iw.iwSize) (hgs.grow (fun q => decRR_mono q) hg04)
      (ConRon.Bridge.Inductives.dRec_ext.list hx4 _ _ hrecsP)
      (ConRon.Bridge.Inductives.dRecOut_ext.list hx4 _ _ hgP))
      (R' := fun rm _ a' => IisPost dn (r3.headD 0) feG _ m4 a4 rm.2 a' ∧ RcMR rm.2 ∧ ownC rm.2 = ownC m4)
      fun rm _ _ hc h => ⟨h, hRc _ (by simp) _ _ _ _ _ (callW_of_callE hc) hR4,
        hOwn _ _ _ _ _ (callW_of_callE hc)⟩)
    fun ⟨r5, m5⟩ _ a5 hrun5 ⟨hP5, hR5, hown5⟩ => ?_
  rw [ctsE.k_stream_recs_check.arm1]
  have hS5 := hP5.stage.stage
  have hg5 := hP5.grow
  -- the pops (the twin's pure fold)
  refine RefE.onlySim (fun _ => ctsE.k_gen_rec_check_pop_all.none ..)
    (Q := fun r m6 => callW p n "gen_rec_check_pop_all" [r3.headD 0, r3.tail.headD 0, r3.tail.tail.headD 0] m5 = some (r, m6))
    (fun r m6 hc => hc) fun r6 m6 c6 => ?_
  have hg45 := hg4.trans hg5
  obtain ⟨s6, hs6, -, hS6, hg6⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
    (genRecCheckPopAll_refines P.rs P.ept P.gpa n _ a5 (r3.headD 0) feG _ _ prevs cs hS5
      (hsp3.grow hg45) (hspc3.grow hg45) (by rw [hown5, hown4]; exact hPop3)) c6
  subst hs6
  have hA6 : AbsOK s6.mem := hAp _ _ _ _ _ c6 hP5.abs
  have hR6 : RcMR s6.mem := hRc _ (by simp) _ _ _ _ _ c6 hR5
  rw [ctsE.k_gen_rec_check_pop_all.arm1]
  have hx5 : ConRon.Arena.Ext a.store a5.store := hx4.trans hP5.core.ext
  have hrel₃ : ConRon.Bridge.Inductives.EnvRel env₂
      (prevs.foldr (fun x acc => acc.popTemp x.1 x.2) feG) a5.store :=
    ConRon.Bridge.Inductives.BT.EnvRel.feq hpop (hrel.mono hx5)
  -- the flush leaving them
  refine RefE.bindSim (fun _ => ctsE.k_flush_caches_2.none ..) (flushSimT P.flush n hS6 hA6)
    fun r7 _ m7 a7 c7 hrun7 ⟨ha7, hS7, hg7, hA7, _⟩ => ?_
  rw [ctsE.k_flush_caches_2.arm1]
  obtain ⟨hck7, i7, hst7⟩ := ConRon.Bridge.Inductives.ReadOK.flush
    (⟨hP5.core.ok.state, hP5.core.ok.pins, hrel₃.ifenv⟩ : ConRon.Bridge.Inductives.ReadOK _ _ a5) hrun7
  have hx7 : ConRon.Arena.Ext a.store a7.store := by rw [hst7]; exact hx5
  refine RefE.ret rfl ⟨StageC.of_checkE hC hS7 hA7 hck7 hx7, by rw [hst7]; exact hrel₃,
    hg04.trans (hg5.trans (hg6.trans hg7)), hA7, hRc _ (by simp) _ _ _ _ _ c7 hR6, ?_⟩
  exact ((p2.toInst.trans i4).trans (hP5.core.toInst)).trans i7

/-- **`check_block_tail_stream`'s contract** (`TsRefS`): `ts_ref` through the call. -/
theorem tsRefS_of {p : Prog} {dn : NIdx → Option ConLeche.Name} (P : TsProg p)
    (hsr : StreamRecsRefS (VerdictCtxU p) p dn)
    (hRc : ∀ f ∈ ["block_rec_infos_tf", "cons_block_recs_temp", "flush_caches", "stream_recs_check",
      "gen_rec_check_pop_all"], RcKeepF p f)
    (hAk : AbsKeep p "cons_block_recs_temp") (hAp : AbsKeep p "gen_rec_check_pop_all")
    (hOwn : OwnKeepF p "stream_recs_check") : TsRefS (VerdictCtxU p) p dn := by
  intro n hn vis fe env₂ m a pp go gl bs bsP gs gsP hC hA hR hrel henvG hbs hrb hp3 hgs hsh hgP
  have h := RefE.ofCallE (s₀ := ⟨m, Locals.init []⟩) (G := VerdictCtxU p) (ctsE_spec p P.look n _ pp vis go gl)
    (fun (hG : VerdictCtxU p) => hG.nv)
    (ts_ref (fun (hG : VerdictCtxU p) => hG.nv) P hsr hRc hAk hAp hOwn n (by omega) hC hA hR hrel henvG hbs
      hrb hp3 hgs hsh hgP)
  refine RefE.callOk h fun ⟨r, m'⟩ x a' _ hR => ?_
  obtain ⟨s', hs', -, hR⟩ := hR
  simp only at hs'; subst hs'
  exact hR

end L.Ind

end
