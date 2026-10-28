import ConAgua.Arena.DeclArmT
import ConAgua.Arena.DeclCanonInfo
import ConAgua.Arena.DeclArmAxiom
import ConAgua.L.ModelGen

/-!
# The axiom arm, both outcomes, under `StageT` (lane `loopt3`, helper `loopt3-axq`)

`check_decl_axiom`'s unified model and refinement `cda_ref`, from `StageT` back to the stage
relation and the core's memos (option (a), replacing the interim contract
`stubArm_keepsCoreMemos`; the quotient arm `check_decl_quot` is `cdq_ref`, `DeclArmQuot.lean`,
and keeps the memos as a leaf).

Every call of the two arms but `check_constant_val` is a leaf of the declaration loop (`leafFns`:
`erec_ci`, the ROM block reader, `quot_pin_hit`, `check_basis_decl`, `ci_canon_eq`,
`std_axiom_ok`, `trust_compiler_ok`, `of_reduce_ax_ok`, `env_push`; `pin_at` is pure). So no
`TwinOK` or con-ron `CheckOK` has to be carried past a core call: the core's memos are kept by the
leaves' frame (`LeafClosed`) and by `erec_ci`'s (`erecCiW_frame`), and given by the one core call,
the constant check, under `StageT` (`ccv_ref`: `TwinOK` at its entry from the arm's `StageT`
across `erec_ci`'s frame). The twin's `StateOK` is needed only at the arm's entry (the ROM
reader, the canonical comparisons), where the loop has it.

The quotient readers' precondition `NamesDn dn a quotNames` (journal `loopt2`, landing 5) comes
from the loop-start fact `QuotDn dn` (`Quot`'s `sortZ` name `u` has a handle under the record
pool's name decoder) and `TwinOK`'s `den.dnN` (that handle reads back to `u` in the twin's name
store); the quotient record's `denoteCV` from the record's denotation (`TwinFold.den`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Arena

open L.Ind
open L.Front (DECL DLP DeclsF)

local notation "V" => ConLeche.CheckMode.verified

/-- **`Quot`'s `sortZ` name has a handle** under the record pool's name decoder `dn` (a fact about
the startup store, state-free; the loop threads it from its start). -/
def QuotDn (dn : NIdx → Option ConLeche.Name) : Prop := ∃ k, dn k = some (.str .anonymous "u")

/-- The quotient readers' precondition from `QuotDn` and the decoder's agreement with the twin's
name store (`TwinMem.dnN`, i.e. `TwinOK.den.dnN`). -/
theorem QuotDn.namesDn {dn : NIdx → Option ConLeche.Name} {m : Mem} {a : AState}
    (hq : QuotDn dn) (hT : TwinMem dn m a) : L.Rom.NamesDn dn a L.Rom.quotNames := by
  intro x hx
  simp only [L.Rom.quotNames, List.mem_cons, List.not_mem_nil, or_false] at hx
  subst hx
  obtain ⟨k, hk⟩ := hq
  exact ⟨k, hk, hT.dnN k _ hk⟩

/-- `erec_ci` keeps the core's memos. -/
theorem erecCiW_memos {n : Nat} {m m' : Mem} {i ck : Word} {r : List Word}
    (h : erecCiW n m i ck = some (r, m')) (hM : CoreMemos m) : CoreMemos m' :=
  hM.frame (erecCiW_frame h) ⟨by decide, by decide⟩ ⟨by decide, by decide⟩

/-- A leaf call keeps the core's memos. -/
theorem leaf_memos {p : Prog} (hcl : LeafClosed p) {f : FnName} (hf : f ∈ leafFns) {k : Nat}
    {args : List Word} {x y : Mem} {rx : List Word} (hc : callW p k f args x = some (rx, y))
    (hM : CoreMemos x) : CoreMemos y :=
  hM.frame (callW_leafFrame hcl hf hc) leafA_memo leafC_memo leafA_walk leafC_walk leafA_lp leafC_lp

/-- **The model of `check_decl_axiom(i, vis)`, both outcomes**: the leaves and pin reads
(outside the verdict closure) lifted, `check_constant_val` by its unified model. -/
l_model checkDeclAxiom_specE (p : Prog) (hX : AxProg p)
  fns [hX.cda ↦ checkDeclAxiomE]
  specs [erecCi_specW p hX.val.rcp n, pinAt_specW p hX.quot.pa n, callW_spec p n "rom_basis_decls",
    callW_spec p n "ci_canon_eq", checkConstantVal_specE p hX.val n, callW_spec p n "std_axiom_ok",
    callW_spec p n "env_push", callW_spec p n "trust_compiler_ok",
    callW_spec p n "of_reduce_ax_ok"]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE]
  heartbeats 400000 simp [] unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What the axiom arm gives besides the twin's environment `fe'` (from `m`): the stage relation
over the result word, the core's memos, the growth. -/
structure CdaPost (dn : NIdx → Option ConLeche.Name) (m : Mem) (r : Word) (m' : Mem) (fe' : IFEnv)
    (a' : AState) : Prop where
  stage : StageR dn r fe' m' a'
  memos : CoreMemos m'
  grow : IWGrow m m'

/-- **The axiom arm refines `checkDecl`'s `.axiomDecl` arm, both outcomes** (con-ron's
`checkDecl_bridge_axiom`'s decomposition), under `StageT`: `Quot.sound` against the pinned block
(installing nothing), else the constant check (`ccv_ref`) and the five recognised axioms;
`propext`/`choice` of another shape and every other axiom decline (the latter after the name's
readback, from the fold invariant), `sorryAx` is skipped. Every other call is a leaf (the core's
memos by its frame). -/
theorem cda_ref {p : Prog} (hX : AxProg p) (hq : KnotStageProg p) (hcl : LeafClosed p)
    (hap : ApdF p) (hkp : CrKeep p) {dn : NIdx → Option ConLeche.Name} (hdn : DnInj dn)
    (hQd : QuotDn dn) {vis : Word} {fe : IFEnv} {a : AState} {n : Nat} (hn : n ≤ 2 ^ 62) {m : Mem}
    {i : Word} {ds : Array IDeclaration} {pins : List INatOpPinSet} {cv : IConstantVal}
    (hS : StageT dn vis fe m a) (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hi : i.toNat < ds.size) (hd : ds[i.toNat] = .axiomDecl cv) (hok : ConRon.Bridge.StateOK a)
    {c : ConLeche.ConstantVal} (hcvd : Frontend.denoteCV a.store cv = some c)
    (hF : ∃ env, ConRon.Bridge.FoldOK V env fe a) (hCr : L.Stubs.CrOK m) :
    RefE (VerdictCtxU p) (checkDeclAxiomE p n m i vis) (checkDecl V pins fe (.axiomDecl cv)) a
      (fun v fe' a' => CdaPost dn m v.1 v.2 fe' a') := by
  have hdecl := hD.recs i.toNat hi
  rw [hd] at hdecl
  obtain ⟨-, hcvAt⟩ := hdecl
  have hlf : ∀ {f : FnName} {k : Nat} {args : List Word} {x y : Mem} {rx : List Word},
      f ∈ cdaLeaves → callW p k f args x = some (rx, y) → CoreMemos x → CoreMemos y :=
    fun {f} _ _ _ _ _ hf hc hx => leaf_memos hcl (by
      simp only [cdaLeaves, List.mem_cons, List.not_mem_nil, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> exact leaf_mem _ rfl) hc hx
  cases n with
  | zero => rw [checkDeclAxiomE.eq_1]; exact RefE.of_cls0 rfl
  | succ n =>
  have hn' : n ≤ 2 ^ 62 := by omega
  rw [checkDeclAxiomE.eq_2]
  unfold checkDecl
  simp only []
  -- `erec_ci`
  rcases h1 : erecCiW n m i 0 with _ | ⟨r1, m1⟩
  · rw [liftE_none, checkDeclAxiomE.k_erec_ci.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, checkDeclAxiomE.k_erec_ci.arm1]
  have hf1 := erecCiW_frame h1
  have hCr1 := CrOK.frame hCr hf1 (by decide) (by decide)
  obtain ⟨hS1, hg1, hci1, hcv1, htop1⟩ := erecCiW_okA h1 hS.stage hD hi hcvAt
  have hT1 : StageT dn vis fe m1 a :=
    ⟨hS1, hS.twin.frame hf1 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩,
      by simp only [pinW, hf1.1 PINS (by decide) (by decide)]; exact hS.flag⟩
  have hM1 : CoreMemos m1 := hT1.twin.memos
  generalize hq0 : r1.headD 0 = q at hci1 hcv1 htop1
  have hqb : q.toNat + 8 < 2 ^ 64 := by
    have := hS1.2.2.1; have := hS1.2.2.2.2.1; omega
  have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_small q 1 (by omega)
  obtain ⟨wn, hwn, hwnl, hname0⟩ := decCI_name hci1
  have hname : cv.name = decI wn := hname0
  rw [rdW_of_get? hq1.symm (erecP_get hwn)]
  -- `Quot.sound`
  rcases h2 : pinAtW m1 4 with _ | ⟨r2, m2⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm2, hr2, hl2, hrun2⟩ := pinAtW_ok h2 hS1.1.pins
  subst hm2
  have ep2 : r2.headD 0 = pinW m2 (1 + (4 : Word).toNat) := by rw [hr2]; rfl
  have hb2 := decI_beq (k := .name) wn _ hwnl hl2
  have hpq : pinQuotSound.run a = .ok (decI (pinW m2 (1 + (4 : Word).toNat)), a) := by
    simpa [pinQuotSound, show PIN_QUOT_SOUND = (4 : Word).toNat from rfl] using hrun2
  refine RefE.bind_right hpq ?_
  rw [hname, hb2]
  have hcv1' : decCV (erecP m2) (q + 1).toNat = some cv := by rw [hq1]; exact hcv1
  by_cases eq2 : wn = r2.headD 0
  · ----- `Quot.sound`
    rw [checkDeclAxiomE.k_pin_at.arm1 p _ _ _ _ _ _ eq2]
    rw [ep2] at eq2
    simp only [eq2, decide_true, ite_true]
    have hN : L.Rom.NamesDn dn a L.Rom.quotNames := hQd.namesDn hS.twin.mem
    rcases h3 : callW p n "rom_basis_decls" [4] m2 with _ | ⟨r3, m3⟩
    · rw [liftE_none, checkDeclAxiomE.k_rom_basis_decls.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨blk, a3, hrun3, hS3, hg3, hD3, -⟩ :=
      hX.quot.rom.quot dn vis fe n m2 a r3 m3 ⟨hS1, hok, hN⟩ h3
    have hM3 := hlf (by simp [cdaLeaves]) h3 hM1
    have hrun3' : (BasisKind.decls .quotK).run a = .ok (blk, a3) := hrun3
    have hok3 := (ConRon.Bridge.BasisKind.decls_run hok hrun3').1
    have hlen : blk.length = (r3.tail.headD 0).toNat := decPL_length (truncM m3) hD3
    refine RefE.bind_right hrun3' ?_
    by_cases hl : r3.tail.headD 0 ≤ 4
    · rw [checkDeclAxiomE.k_rom_basis_decls.abort1 p _ _ _ _ _ hl]
      have hn4 : blk[4]? = none := by
        apply List.getElem?_eq_none; rw [hlen]
        have := UInt64.le_iff_toNat_le.mp hl; simpa using this
      rw [hn4]
      exact fun _ => ErrClaim.fail _ _ rfl
    rw [checkDeclAxiomE.k_rom_basis_decls.arm1 p _ _ _ _ _ hl]
    generalize r3.headD 0 = o3 at hD3 ⊢
    generalize r3.tail.headD 0 = l3 at hD3 hlen hl
    have hlt : 4 < l3.toNat := by
      have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hl); simpa using this
    obtain ⟨v, ci, hv, hci, hget⟩ := decPL_get _ _ _ hD3 4 hlt
    have hvm : iwN m3 (o3.toNat + 4) = some v := (IWGrow.refl m3).truncExt.1.nat? hv
    obtain ⟨w, hw, rfl⟩ : ∃ w, (iwA m3)[o3.toNat + 4]? = some w ∧ w.toNat = v := by
      simp only [iwN, nat?, Option.map_eq_some_iff] at hvm; exact hvm
    have hob : o3.toNat + 4 < 2 ^ 64 := by
      have := (Array.getElem?_eq_some_iff.mp hw).1; have := hS3.2.2.2.1; simp only [iwA] at *; omega
    have ew : rdW (m3.arr64 IW) (o3 + 4) = w := by
      have : (o3 + 4).toNat = o3.toNat + 4 := by
        rw [UInt64.toNat_add]; simp; omega
      simp only [rdW, this]; simp only [iwA] at hw; simp [hw]
    rw [ew, hget]
    rcases h4 : callW p n "ci_canon_eq" [q, w] m3 with _ | ⟨r4, m4⟩
    · rw [liftE_none, checkDeclAxiomE.k_ci_canon_eq.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨s4, hs4, -, hok4, ⟨⟨hS4, hg4, hb4, -⟩, -⟩, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (ciCanonEq_refines p hX.quot.canon dn vis fe q w (.axiomInfo cv) ci n ⟨m3, Locals.init []⟩ a3
        ⟨hS3, ArrExt.decCI (IWGrow.erecPExt hg3) hci1, ArrExt.decCI (truncM_erecP m3) hci,
          poolSmall_of_stage hS3, fun x y l hx hy => hok3.view_inj hx hy⟩) h4
    subst hs4
    have hrun4 := AM.run_of_ok _ _ hok4
    refine RefE.bind_right hrun4 ?_
    by_cases z4 : r4.headD 0 = 0
    · rw [checkDeclAxiomE.k_ci_canon_eq.abort1 p _ _ _ z4]
      have hb : AM.res ((IConstantInfo.axiomInfo cv).canonEq ci) a3 = false := by
        rw [← hb4, z4]; rfl
      rw [hb]
      exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
    rw [checkDeclAxiomE.k_ci_canon_eq.arm1 p _ _ _ z4]
    have hb : AM.res ((IConstantInfo.axiomInfo cv).canonEq ci) a3 = true := by
      rw [← hb4]; simpa using z4
    rw [hb]
    exact RefE.ite_pos rfl (RefE.ret rfl ⟨by simpa using hS4,
      hlf (by simp [cdaLeaves]) h4 hM3, hg1.trans (hg3.trans hg4)⟩)
  ----- the ordinary axioms
  rw [checkDeclAxiomE.k_pin_at.arm2 p _ _ _ _ _ _ eq2]
  rw [ep2] at eq2
  simp only [eq2, decide_false, Bool.false_eq_true, ite_false]
  -- the constant check
  have h3R := ccv_ref hq hap hkp hn' hT1 hcv1' (by omega) (denoteCV_lps hcvd) hCr1
  rcases h3 : checkConstantValE p n m2 vis (q + 1) with e3 | ⟨r3, m3⟩ <;> rw [h3] at h3R
  · rw [checkDeclAxiomE.k_check_constant_val.none]; exact RefE.bind_left h3R
  rw [checkDeclAxiomE.k_check_constant_val.arm1]
  obtain ⟨_, a3, hrun3, hP3⟩ := h3R
  have hS3 := hP3.stage
  have hg3 := hP3.grow
  obtain ⟨env, hFo⟩ := hF
  obtain ⟨hstep1, -, -⟩ :=
    ConRon.Bridge.checkConstantVal_bridge_of_fold rfl (ConRon.Bridge.CoreSpec.of_core rfl) hFo hcvd hrun3
  have hok1 := hFo.ofCore hstep1
  have hcA := ConRon.Bridge.denoteCV_ext hcvd hstep1.ext
  have hnmA : denoteN a.store.ns (decI wn) = some c.name := by
    rw [← hname]; exact (ConRon.Bridge.denoteCV_inv hcvd).1
  have hext1 := hstep1.ext
  refine RefE.bind_right hrun3 ?_
  have hPx : ArrExt (erecP m2) (erecP m3) := IWGrow.erecPExt hg3
  have hM3 : CoreMemos m3 := hS3.twin.memos
  -- the standard axioms
  rcases h4 : callW p n "std_axiom_ok" [vis, q + 1] m3 with _ | ⟨r4, m4⟩
  · rw [liftE_none, checkDeclAxiomE.k_std_axiom_ok.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨s4, hs4, -, hok4, hS4, hg4, hb4, -⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (stdAxiomOk_refines p hX.std dn hdn vis fe (q + 1) cv n ⟨m3, Locals.init []⟩ a3
      ⟨hS3.stage, ArrExt.decCV hPx hcv1'⟩) h4
  subst hs4
  have hM4 := hlf (by simp [cdaLeaves]) h4 hM3
  have hrun4 := AM.run_of_ok _ _ hok4
  refine RefE.bind_right hrun4 ?_
  generalize s4.mem = m4 at *
  generalize AM.res (stdAxiomOk fe cv) a3 = b4 at hrun4 hb4
  generalize AM.st (stdAxiomOk fe cv) a3 = a4 at hrun4 hS4
  obtain ⟨-, hext4, hcache4, -, -⟩ := ConRon.Bridge.stdAxiomOk_run hok1 hcA hrun4
  have hP4 : ArrExt (erecP m2) (erecP m4) := IWGrow.erecPExt (hg3.trans hg4)
  -- a push of the axiom, after a passed test
  have push : ∀ {mx : Mem} {ax : AState}, StageR dn vis fe mx ax → IWGrow m2 mx → CoreMemos mx →
      RefE (VerdictCtxU p) (checkDeclAxiomE.k_env_push p (liftE (callW p n "env_push" [vis, q] mx)))
        (pure (fe.push (.axiomInfo cv)) : AM IFEnv) ax
        (fun v fe' a' => CdaPost dn m v.1 v.2 fe' a') := by
    intro mx ax hSx hgx hMx
    rcases e : callW p n "env_push" [vis, q] mx with _ | ⟨ry, my⟩
    · rw [liftE_none, checkDeclAxiomE.k_env_push.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some, checkDeclAxiomE.k_env_push.arm1]
    obtain ⟨hSy, hgy⟩ := push_call hX.val.rcp e hSx (ArrExt.decCI (IWGrow.erecPExt hgx) hci1)
    exact RefE.ret rfl ⟨by simpa using hSy, hlf (by simp [cdaLeaves]) e hMx,
      hg1.trans (hgx.trans hgy)⟩
  by_cases z4 : r4.headD 0 ≠ 0
  · rw [checkDeclAxiomE.k_std_axiom_ok.arm1 p _ _ _ _ _ _ z4]
    have hb : b4 = true := by rw [← hb4]; simpa using z4
    rw [hb]
    exact RefE.ite_pos rfl (push hS4 (hg3.trans hg4) hM4)
  have z4' : r4.headD 0 = 0 := by simpa using z4
  rw [checkDeclAxiomE.k_std_axiom_ok.arm2 p _ _ _ _ _ _ z4']
  have hb : b4 = false := by rw [← hb4, z4']; rfl
  rw [hb]
  refine RefE.ite_neg (by decide) ?_
  -- `Lean.trustCompiler`
  rcases h5 : pinAtW m4 42 with _ | ⟨r5, m5⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at_2.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm5, hr5, hl5, hrun5⟩ := pinAtW_ok h5 hS4.1.pins
  subst hm5
  have ep5 : r5.headD 0 = pinW m5 (1 + (42 : Word).toNat) := by rw [hr5]; rfl
  have hb5 := decI_beq (k := .name) wn _ hwnl hl5
  have htn : trustCompilerName.run a4 = .ok (decI (pinW m5 (1 + (42 : Word).toNat)), a4) := by
    simpa [trustCompilerName, pinTrustCompiler, show PIN_TRUST_COMPILER = (42 : Word).toNat from rfl]
      using hrun5
  refine RefE.bind_right htn ?_
  rw [hb5]
  by_cases eq5 : wn = r5.headD 0
  · rw [checkDeclAxiomE.k_pin_at_2.arm1 p _ _ _ _ _ _ eq5]
    rw [ep5] at eq5
    simp only [eq5, decide_true, ite_true]
    rcases h6 : callW p n "trust_compiler_ok" [vis, q + 1] m5 with _ | ⟨r6, m6⟩
    · rw [liftE_none, checkDeclAxiomE.k_trust_compiler_ok.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨s6, hs6, -, hok6, hS6, hg6, hb6, -⟩ := triple_of_callW (s₀ := ⟨m5, Locals.init []⟩)
      (trustCompilerOk_refines p hX.tco dn vis fe (q + 1) cv n ⟨m5, Locals.init []⟩ a4
        ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) h6
    subst hs6
    have hrun6 := AM.run_of_ok _ _ hok6
    refine RefE.bind_right hrun6 ?_
    by_cases z6 : r6.headD 0 = 0
    · rw [checkDeclAxiomE.k_trust_compiler_ok.abort1 p _ _ _ _ _ z6]
      have ht6 : AM.res (trustCompilerOk fe cv) a4 = false := by rw [← hb6, z6]; rfl
      rw [ht6]
      exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
    rw [checkDeclAxiomE.k_trust_compiler_ok.arm1 p _ _ _ _ _ (by simpa using z6)]
    have ht6 : AM.res (trustCompilerOk fe cv) a4 = true := by rw [← hb6]; simpa using z6
    rw [ht6]
    exact RefE.ite_pos rfl (push hS6 (hg3.trans (hg4.trans hg6))
      (hlf (by simp [cdaLeaves]) h6 hM4))
  rw [checkDeclAxiomE.k_pin_at_2.arm2 p _ _ _ _ _ _ eq5]
  rw [ep5] at eq5
  simp only [eq5, decide_false, Bool.false_eq_true, ite_false]
  -- the `ofReduce*` pair
  rcases h7 : pinAtW m5 45 with _ | ⟨r7, m7⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at_3.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, checkDeclAxiomE.k_pin_at_3.arm1]
  obtain ⟨hm7, hr7, hl7, hrun7⟩ := pinAtW_ok h7 hS4.1.pins
  subst hm7
  have ep7 : r7.headD 0 = pinW m7 (1 + (45 : Word).toNat) := by rw [hr7]; rfl
  rcases h8 : pinAtW m7 46 with _ | ⟨r8, m8⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at_4.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm8, hr8, hl8, hrun8⟩ := pinAtW_ok h8 hS4.1.pins
  subst hm8
  have ep8 : r8.headD 0 = pinW m8 (1 + (46 : Word).toNat) := by rw [hr8]; rfl
  have hb7 := decI_beq (k := .name) wn _ hwnl hl7
  have hb8 := decI_beq (k := .name) wn _ hwnl hl8
  have hon : ofReduceNatName.run a4 = .ok (decI (pinW m8 (1 + (45 : Word).toNat)), a4) := by
    simpa [ofReduceNatName, pinOfReduceNat, show PIN_OF_REDUCE_NAT = (45 : Word).toNat from rfl]
      using hrun7
  have hob : ofReduceBoolName.run a4 = .ok (decI (pinW m8 (1 + (46 : Word).toNat)), a4) := by
    simpa [ofReduceBoolName, pinOfReduceBool, show PIN_OF_REDUCE_BOOL = (46 : Word).toNat from rfl]
      using hrun8
  refine RefE.bind_right hon (RefE.bind_right hob ?_)
  by_cases eq8 : wn = r7.headD 0 ∨ wn = r8.headD 0
  · rw [checkDeclAxiomE.k_pin_at_4.arm1 p _ _ _ _ _ _ _ eq8]
    rw [ep7, ep8] at eq8
    have hor : ((decI wn : NIdx) == decI (pinW m8 (1 + (45 : Word).toNat)) ||
        (decI wn : NIdx) == decI (pinW m8 (1 + (46 : Word).toNat))) = true := by
      rw [hb7, hb8]; rcases eq8 with e | e <;> simp [e]
    rw [hor]
    refine RefE.ite_pos rfl ?_
    rcases h9 : callW p n "of_reduce_ax_ok" [vis, q + 1] m8 with _ | ⟨r9, m9⟩
    · rw [liftE_none, checkDeclAxiomE.k_of_reduce_ax_ok.none]; exact RefE.of_cls0 (by simp)
    rw [liftE_some]
    obtain ⟨s9, hs9, -, hok9, hS9, hg9, hb9, -⟩ := triple_of_callW (s₀ := ⟨m8, Locals.init []⟩)
      (ofReduceAxOk_refines p hX.ora dn hdn vis fe (q + 1) cv n ⟨m8, Locals.init []⟩ a4
        ⟨hS4, ArrExt.decCV hP4 hcv1'⟩) h9
    subst hs9
    have hrun9 := AM.run_of_ok _ _ hok9
    refine RefE.bind_right hrun9 ?_
    by_cases z9 : r9.headD 0 = 0
    · rw [checkDeclAxiomE.k_of_reduce_ax_ok.abort1 p _ _ _ _ _ z9]
      have ht9 : AM.res (ofReduceAxOk fe cv) a4 = false := by rw [← hb9, z9]; rfl
      rw [ht9]
      exact RefE.ite_neg (by decide) fun _ => ErrClaim.fail _ _ rfl
    rw [checkDeclAxiomE.k_of_reduce_ax_ok.arm1 p _ _ _ _ _ (by simpa using z9)]
    have ht9 : AM.res (ofReduceAxOk fe cv) a4 = true := by rw [← hb9]; simpa using z9
    rw [ht9]
    exact RefE.ite_pos rfl (push hS9 (hg3.trans (hg4.trans hg9))
      (hlf (by simp [cdaLeaves]) h9 hM4))
  rw [checkDeclAxiomE.k_pin_at_4.arm2 p _ _ _ _ _ _ _ eq8]
  rw [ep7, ep8] at eq8
  have hor : ((decI wn : NIdx) == decI (pinW m8 (1 + (45 : Word).toNat)) ||
      (decI wn : NIdx) == decI (pinW m8 (1 + (46 : Word).toNat))) = false := by
    rw [hb7, hb8]; simp only [not_or] at eq8
    simp only [decide_eq_false eq8.1, decide_eq_false eq8.2, Bool.or_false]
  rw [hor]
  refine RefE.ite_neg (by decide) ?_
  -- `propext` / `choice` of another shape
  rcases h10 : pinAtW m8 32 with _ | ⟨r10, m10⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at_5.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some, checkDeclAxiomE.k_pin_at_5.arm1]
  obtain ⟨hm10, hr10, hl10, hrun10⟩ := pinAtW_ok h10 hS4.1.pins
  subst hm10
  have ep10 : r10.headD 0 = pinW m10 (1 + (32 : Word).toNat) := by rw [hr10]; rfl
  rcases h11 : pinAtW m10 33 with _ | ⟨r11, m11⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at_6.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm11, hr11, hl11, hrun11⟩ := pinAtW_ok h11 hS4.1.pins
  subst hm11
  have ep11 : r11.headD 0 = pinW m11 (1 + (33 : Word).toNat) := by rw [hr11]; rfl
  have hb10 := decI_beq (k := .name) wn _ hwnl hl10
  have hb11 := decI_beq (k := .name) wn _ hwnl hl11
  have hpn : propextName.run a4 = .ok (decI (pinW m11 (1 + (32 : Word).toNat)), a4) := by
    simpa [propextName, pinPropext, show PIN_PROPEXT = (32 : Word).toNat from rfl] using hrun10
  have hch : choiceName.run a4 = .ok (decI (pinW m11 (1 + (33 : Word).toNat)), a4) := by
    simpa [choiceName, pinChoice, show PIN_CHOICE = (33 : Word).toNat from rfl] using hrun11
  refine RefE.bind_right hpn (RefE.bind_right hch ?_)
  by_cases eq11 : wn = r10.headD 0 ∨ wn = r11.headD 0
  · rw [checkDeclAxiomE.k_pin_at_6.abort1 p _ _ _ _ _ eq11]
    rw [ep10, ep11] at eq11
    have hor2 : ((decI wn : NIdx) == decI (pinW m11 (1 + (32 : Word).toNat)) ||
        (decI wn : NIdx) == decI (pinW m11 (1 + (33 : Word).toNat))) = true := by
      rw [hb10, hb11]; rcases eq11 with e | e <;> simp [e]
    rw [hor2]
    exact RefE.ite_pos rfl fun _ => ErrClaim.fail _ _ rfl
  rw [checkDeclAxiomE.k_pin_at_6.arm1 p _ _ _ _ _ eq11]
  rw [ep10, ep11] at eq11
  have hor2 : ((decI wn : NIdx) == decI (pinW m11 (1 + (32 : Word).toNat)) ||
      (decI wn : NIdx) == decI (pinW m11 (1 + (33 : Word).toNat))) = false := by
    rw [hb10, hb11]; simp only [not_or] at eq11
    simp only [decide_eq_false eq11.1, decide_eq_false eq11.2, Bool.or_false]
  rw [hor2]
  refine RefE.ite_neg (by decide) ?_
  -- `sorryAx` is skipped
  rcases h12 : pinAtW m11 13 with _ | ⟨r12, m12⟩
  · rw [liftE_none, checkDeclAxiomE.k_pin_at_7.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hm12, hr12, hl12, hrun12⟩ := pinAtW_ok h12 hS4.1.pins
  subst hm12
  have ep12 : r12.headD 0 = pinW m12 (1 + (13 : Word).toNat) := by rw [hr12]; rfl
  have hb12 := decI_beq (k := .name) wn _ hwnl hl12
  have hsa : pinSorryAx.run a4 = .ok (decI (pinW m12 (1 + (13 : Word).toNat)), a4) := by
    simpa [pinSorryAx, show PIN_SORRY_AX = (13 : Word).toNat from rfl] using hrun12
  refine RefE.bind_right hsa ?_
  rw [hb12]
  by_cases eq12 : wn = r12.headD 0
  · rw [checkDeclAxiomE.k_pin_at_7.arm1 p _ _ _ _ eq12]
    rw [ep12] at eq12
    simp only [eq12, decide_true, ite_true]
    exact RefE.ret rfl ⟨by simpa using hS4, hM4, hg1.trans (hg3.trans hg4)⟩
  rw [checkDeclAxiomE.k_pin_at_7.abort1 p _ _ _ _ eq12]
  rw [ep12] at eq12
  rw [decide_eq_false eq12]
  refine RefE.ite_neg (by decide) ?_
  -- the readback of the name
  have hrn4 : ReadNCOK a4 := fun h x e =>
    ConRon.Bridge.denoteN_ext (hok1.check.caches.readN h x (by rw [← hcache4]; exact e)) hext4
  have hnm4 : denoteN a4.store.ns (decI wn) = some c.name :=
    ConRon.Bridge.denoteN_ext (ConRon.Bridge.denoteN_ext hnmA hext1) hext4
  obtain ⟨X, hrunN, -⟩ := readNameM_run' a4 (decI wn) c.name hnm4 hrn4
  exact RefE.bind_right hrunN fun _ => ErrClaim.fail _ _ rfl

end L.Arena
