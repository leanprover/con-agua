import ConAgua.Arena.RecGenSpec.CfhW
import ConAgua.Arena.RecClassSpec.ClassNPcOf
import ConAgua.Arena.RecGenSpec.ClassFieldsOf
import ConAgua.Arena.IndRealAbsPos
import ConAgua.Arena.IndRealAbsSim
import ConAgua.Arena.RecClassSpec.SlotProg
import ConAgua.Arena.GrindAttr
import ConAgua.L.ModelGen

/-!
# `class_fields_of_go`, `class_fields_of`: one model and one refinement for both outcomes

`cfgE` (`l_model … unified`): the recursive call through the model itself, the callees (all outside
the verdict closure) through their `Option` models. `cfg_ref` refines `classFieldsOf` for both
outcomes: an error comes from the single abort (`R_GENERATED_RECURSOR_THE_INDUCTIVE`, the twin's
`fail`) or is of class `0`. `class_fields_of`'s unified model `cfoE` calls it in tail position
(`cfo_ref`); its callers read `cfo_ref` through the run (`RefE.run_okW`, `RefE.run_err`).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

l_model cfgE_spec (p : Prog) (hP : CfoProg p)
  fns [hP.go ↦ cfgE]
  specs [ftdF_spec0 p hP.ftd n, nestOcc_spec' p hP.no n, classFieldsOfHits_spec p hP.hits n,
    iwAlloc_specW p hP.alloc n, piBinders_spec p hP.alloc hP.copy hP.no.hv hP.cons hP.pb n,
    rec3_specW p hP.alloc n hP.r3, slCons_specW p hP.alloc hP.copy hP.cons n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

/-- What `class_fields_of_go` gives besides the twin's kinds `ks` (from `m`): the stage relation,
growth, the kinds a slice stable above `m`'s top, `nest_occ`'s memo relation at some map, the
write set outside the other walk memos, the abstraction memo's frame. -/
structure CfgPost (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (m : Mem) (r : List Word)
    (m' : Mem) (ks : List ClassField) (a' : AState) : Prop where
  stage : StageR dn vis fe m' a'
  grow : IWGrow m m'
  kinds : SPLA (iwTop m) decCF m' (r.headD 0).toNat (r.tail.headD 0).toNat ks
  nomr : ∃ mp, noMR m' mp
  frame : MFr [NOM] [204, 205] m m'
  afr : AFr m m'

section sims
variable {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
variable {p : Prog}

/-- The common tail of both arms: the record, the rest (the recursive call), the cons. -/
theorem cfgTailE {G : Prop} {n : Nat} {m m2 m5 : Mem} {a2 : AState} {k : Word} {ws r5 : List Word}
    {y : ClassField} {mp : Std.HashMap EIdx Bool} {mo ml io il i fo fl : Word}
    {opR : AM (List ClassField)}
    (hS2 : StageR dn vis fe m2 a2) (hg2 : IWGrow m m2) (hM2 : noMR m2 mp)
    (hf2 : MFr [NOM] [204, 205] m m2) (hA2 : AFr m m2) (hk : k.toNat = ws.length)
    (hy : ∀ m'', (∀ j (hj : j < ws.length), iwN m'' ((rdW (m2.arr64 CTL) 200).toNat + j) = some (ws[j]'hj).toNat) →
      decCF m'' (rdW (m2.arr64 CTL) 200).toNat = some y)
    (h5 : recW m2 k ws = some (r5, m5))
    (hrest : StageR dn vis fe m5 a2 → IWGrow m2 m5 → noMR m5 mp →
      RefE G (cfgE p n m5 mo ml io il (i + 1) (fo + 1) (fl - 1)) opR a2
        (fun v ks a' => CfgPost dn vis fe m5 v.1 v.2 ks a')) :
    RefE G (cfgE.j1 p n mo ml io il i fo fl (r5.headD 0) m5) (do let r ← opR; pure (y :: r)) a2
      (fun v ks a' => CfgPost dn vis fe m v.1 v.2 ks a') := by
  have hc := hS2.iw.ctl
  have hsz := hS2.iw.iwSize
  obtain ⟨hr5, -, hg5, hf5, htop5, hroom5⟩ := recW_post h5 hc hsz hk
  have hS5 := stage_frame_iw hS2 hf5 (by omega)
  have hy5 := rec2RecW_decCF_A (b := iwTop m) h5 hc hsz hk hg2.iw (by rw [hr5]; exact hy)
  have hR := hrest hS5 hg5 (rec2NoMR_iw hf5 hM2)
  rw [cfgE.j1.arm1]
  refine RefE.bindE (fun _ => cfgE.k_class_fields_of_go.none ..) id hR fun ⟨r6, m6⟩ _ _ _ hP6 => ?_
  rw [cfgE.k_class_fields_of_go.arm1]
  refine RefE.onlySim (fun _ => cfgE.k_sl_cons.none ..) (fun _ _ h => h) fun r7 m7 h7 => ?_
  rw [cfgE.k_sl_cons.arm1]
  have hsp6 := hP6.kinds
  obtain ⟨mp6, hM6⟩ := hP6.nomr
  obtain ⟨hS7, hg7, hsp7⟩ := SPLA.cons h7 hP6.stage (hsp6.mono (Nat.le_trans hg2.iw hg5.iw))
    (Nat.le_trans hg2.iw (Nat.le_trans hg5.iw hP6.grow.iw)) (hy5.grow (AgreeA.of_grow hP6.grow))
  obtain ⟨-, hsb, ps, hps, -⟩ := hsp6
  obtain ⟨-, -, -, hf7, -⟩ := consW_decN h7 hP6.stage.iw.iwSize hP6.stage.iw.ctl hsb hps
  exact RefE.ret rfl ⟨hS7, hg2.trans (hg5.trans (hP6.grow.trans hg7)), by simpa using hsp7,
    ⟨mp6, rec2NoMR_iw hf7 hM6⟩, hf2.trans ((MFr.of_iw hf5).up.trans (hP6.frame.trans (MFr.of_iw hf7).up)),
    hA2.trans ((recW_afr h5).trans (hP6.afr.trans (consW_afr h7)))⟩

/-- **`class_fields_of_go` refines `classFieldsOf`, both outcomes** (twin side: the list recursion
of `classFieldsOf`): `fvar_type_d`, `nest_occ`, the hits, then the field's kind (an ordinary
field's one-word record, or a recursive field's `pi_binders` and three-word record), the rest, the
cons; the one reject site (neither kind) is the twin's `fail`. -/
theorem cfg_ref (bsh : BlockShape) (ihs : List (Nat × Nat)) (n : Nat) :
    ∀ {m : Mem} {a : AState} {mo ml io il i fo fl : Word} {fs : List EIdx}
    {mp0 : Std.HashMap EIdx Bool},
    StageR dn vis fe m a →
    decHL m mo.toNat ml.toNat = some bsh.memberNames → mo.toNat + ml.toNat ≤ iwTop m →
    StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs → io.toNat + il.toNat < 2 ^ 64 →
    decHL m fo.toNat fl.toNat = some fs → fo.toNat + fl.toNat ≤ iwTop m →
    i.toNat + fl.toNat < 2 ^ 64 → noMR m mp0 →
    RefE (closedNV p _root_.L.Checker.nvFns = true) (cfgE p n m mo ml io il i fo fl)
      (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a
      (fun v ks a' => CfgPost dn vis fe m v.1 v.2 ks a') := by
  induction n with
  | zero =>
    intro m a mo ml io il i fo fl fs mp0 _ _ _ _ _ _ _ _ _
    rw [cfgE.eq_def]
    exact RefE.of_cls0 (by simp)
  | succ n ih =>
  intro m a mo ml io il i fo fl fs mp0 hS hmn hmb hih hib hfs hfb hi hM
  have hsz := hS.iw.iwSize
  have htop := hS.iw.iw
  by_cases hfl : fl = 0
  · rw [cfgE.arm1 p n m mo ml io il i fo fl hfl]
    obtain rfl : fs = [] := by
      have := decHL_length m hfs; rw [hfl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    rw [ConRon.Arena.classFieldsOf]
    exact RefE.ret rfl ⟨hS, IWGrow.refl m,
      (by simpa using SPLA.nil (b := iwTop m) (dec := decCF) (m := m) 0 (by omega)), ⟨mp0, hM⟩,
      MFr.refl _ _ _, AFr.refl _⟩
  rw [cfgE.arm2 p n m mo ml io il i fo fl hfl]
  obtain ⟨w0, fs', rfl, hw0, hw0H, hfs'⟩ := decHL_cons hfs hfl (by omega)
  subst hw0
  obtain ⟨hsum, hfo1⟩ := toNat_succ_of_lt (o := fo) (l := fl) (by omega) hfl
  have hfl1 : (fl - 1).toNat + 1 = fl.toNat := by omega
  have hi1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  rw [ConRon.Arena.classFieldsOf]
  -- `fvar_type_d`
  refine RefE.bindSim (fun _ => cfgE.k_fvar_type_d.none ..) (fun r m h => simFvarTypeD hS hw0H (r, m) h)
    fun r1 _ m1 a1 h1 _ ⟨hS1, hg1, hwH, hwd⟩ => ?_
  rw [cfgE.k_fvar_type_d.arm1]
  dsimp only at hS1 hg1 hwH hwd
  subst hwd
  have hM1 := rec2NoMR_ftd h1 hM
  -- `nest_occ`
  refine RefE.bindSim (fun _ => cfgE.k_nest_occ.none ..) (fun r m h =>
      rec2SimNestOcc hS1 hwH (by rw [decHL_grow hg1 hmb]; exact hmn) (by omega) hM1 n (r, m) h)
    fun occ b m2 a2 h2 _ ⟨ha2, hob, hM2, hS2, hg2, hf2⟩ => ?_
  rw [cfgE.k_nest_occ.arm1]
  subst a2
  dsimp only at hob hM2 hS2 hg2 hf2
  have hf12 : MFr [NOM] [204, 205] m m2 := (MFr.of_frame (ftdF_frame h1) (by simp) (by simp)).up.trans hf2
  have hg12 := hg1.trans hg2
  have hA12 : AFr m m2 := (ftdF_afr h1).trans (noConstWf_afr h2)
  -- `class_fields_of_hits`
  rcases h3 : cfhW n m2 io il i with _ | ⟨hc, cls⟩
  · rw [liftE_none, cfgE.k_class_fields_of_hits.none]; exact RefE.of_cls0 (by simp)
  rw [liftE_some]
  obtain ⟨hcnt, hcls⟩ := cfhW_ok n m2 io il i hc cls ihs h3 (hih m2 hg12) hib hS2.iw.iwSize
  have hrest : ∀ m5, StageR dn vis fe m5 a1 → IWGrow m2 m5 → noMR m5 ∅ →
      RefE (closedNV p _root_.L.Checker.nvFns = true) (cfgE p n m5 mo ml io il (i + 1) (fo + 1) (fl - 1))
        (ConRon.Arena.classFieldsOf bsh ihs (i.toNat + 1) fs') a1
        (fun v ks a' => CfgPost dn vis fe m5 v.1 v.2 ks a') := by
    intro m5 hS5 hg5 hM5
    have hg := hg12.trans hg5
    have := ih (m := m5) (a := a1) (i := i + 1) (fo := fo + 1) (fl := fl - 1) hS5
      (by rw [decHL_grow hg hmb]; exact hmn) (Nat.le_trans hmb hg.iw) (hih.grow hg) hib
      (by rw [decHL_grow hg (by omega)]; exact hfs') (by have := hg.iw; omega) (by omega) hM5
    rwa [hi1] at this
  by_cases hA : occ = 0 ∧ hc = 0
  · rw [cfgE.k_class_fields_of_hits.arm1 p n _ _ _ _ _ _ _ _ _ _ _ _ hA]
    have hb : b = false := by rw [← hob, hA.1]; rfl
    have hlen : (List.filter (fun h => h.1 == i.toNat) ihs).length = 0 := by rw [← hcnt, hA.2]; rfl
    subst hb
    simp only [hlen, Bool.not_false, Bool.true_and, beq_self_eq_true, ite_true]
    refine RefE.onlySim (fun _ => cfgE.k_iw_alloc.none ..) (fun _ _ h => h) fun cf m4 h4 => ?_
    rw [cfgE.k_iw_alloc.arm1]
    have h5 : recW m2 1 [0] = some ([cf], m4.set64 IW cf 0) := by simp [recW, h4, wrIW]
    refine cfgTailE hS2 hg12 hM2 hf12 hA12 rfl ?_ h5 (hrest _)
    intro m'' hw
    have := hw 0 (by simp)
    simp only [decCF]; simp at this; rw [this]; rfl
  by_cases hB : occ ≠ 0 ∧ hc = 1
  · rw [cfgE.k_class_fields_of_hits.arm2 p n _ _ _ _ _ _ _ _ _ _ _ _ hA hB]
    have hb : b = true := by rw [← hob]; simpa using hB.1
    have hlen : (List.filter (fun h => h.1 == i.toNat) ihs).length = 1 := by rw [← hcnt, hB.2]; rfl
    subst hb
    obtain ⟨hh, hhs⟩ := List.length_eq_one_iff.mp hlen
    obtain ⟨hcl, hcl64⟩ := hcls hh hhs
    simp only [hhs, Bool.not_true, Bool.false_and, Bool.true_and,
      ite_false, Bool.false_eq_true]
    refine RefE.bindSim (fun _ => cfgE.k_pi_binders.none ..) (fun r m h => rec2SimPiBinders n hS2 hwH (r, m) h)
      fun r4 ⟨bs, e⟩ m4 a4 h4 _ ⟨ha4, hS4, hg4, hf4, hd4⟩ => ?_
    rw [cfgE.k_pi_binders.arm1]
    subst a4
    dsimp only at hS4 hg4 hf4 hd4
    refine RefE.onlySim (fun _ => cfgE.k_rec3.none ..) (fun _ _ h => h) fun r5 m5 h5 => ?_
    rw [cfgE.k_rec3.arm1]
    have hbl : bs.length = (r4.tail.headD 0).toNat := decHL_length _ hd4
    refine cfgTailE hS4 (hg12.trans hg4) (rec2NoMR_iw hf4 hM2) (hf12.trans (MFr.of_iw hf4).up)
      (hA12.trans (piBW_afr _ _ _ _ _ _ h4)) rfl ?_ h5
      (fun hS5 hg5 hM5 => hrest _ hS5 (hg4.trans hg5) hM5)
    intro m'' hw
    have h0 := hw 0 (by simp)
    have h1 := hw 1 (by simp)
    have h2 := hw 2 (by simp)
    simp at h0 h1 h2
    simp only [decCF, h0, h1, h2, List.getD_cons_zero, hcl, UInt64.toNat_ofNat_of_lt' hcl64, hbl]
    rcases r4 with _ | ⟨x0, _ | ⟨x1, t⟩⟩ <;> rfl
  rw [cfgE.k_class_fields_of_hits.abort1 p n _ _ _ _ _ _ _ _ _ _ _ _ hA hB]
  intro _
  have hc0 := hcnt
  cases b with
  | false =>
    have h20 : occ = 0 := by simpa using hob
    have h30 : (hc).toNat ≠ 0 := fun h =>
      hA ⟨h20, UInt64.toNat_inj.mp (by simpa using h)⟩
    simp only [← hc0, h30, Bool.not_false, Bool.true_and, beq_iff_eq, Bool.false_and, ite_false]
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.fail _ _ (by decide)
  | true =>
    have h20 : occ ≠ 0 := by simpa using hob
    have h30 : (hc).toNat ≠ 1 := fun h =>
      hB ⟨h20, UInt64.toNat_inj.mp (by simpa using h)⟩
    simp only [← hc0, h30, Bool.not_true, Bool.false_and, Bool.true_and, beq_iff_eq, ite_false]
    simp only [Bool.false_eq_true, ite_false]
    exact ErrClaim.fail _ _ (by decide)

end sims

/-! ## `class_fields_of` -/

l_model cfoE_spec (p : Prog) (hP : CfoProg p)
  fns [hP.cfo ↦ cfoE]
  specs [blockShapeMemberNames_spec p hP.alloc hP.mnc hP.mn n, cfgE_spec p hP n]
  grind [arena_grind] fold [tierW, idxW]
  extra [ld64_rdW_specE, evalE_tld, tld, evalE_cnt, tcntM, evalE_tierE, evalE_idxE, evalE_idxAE, evalE_tagE]
  heartbeats 4000000 unified
  nv [closedNV p _root_.L.Checker.nvFns = true, _root_.L.Checker.nv_mem]

section cfo
variable {p : Prog} (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)

/-- **`class_fields_of` refines `classFieldsOf`, both outcomes**: the block's member names
(`block_shape_member_names`, outside the verdict closure), then `class_fields_of_go` (`cfg_ref`) in
tail position. -/
theorem cfo_ref (bsh : BlockShape) (ihs : List (Nat × Nat)) (n : Nat) {m : Mem} {a : AState}
    {q io il i fo fl : Word} {fs : List EIdx} {mp0 : Std.HashMap EIdx Bool} (hS : StageR dn vis fe m a)
    (hb : BSOK m q.toNat bsh) (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) m ihs)
    (hib : io.toNat + il.toNat < 2 ^ 64) (hfs : decHL m fo.toNat fl.toNat = some fs)
    (hfb : fo.toNat + fl.toNat ≤ iwTop m) (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR m mp0) :
    RefE (closedNV p _root_.L.Checker.nvFns = true) (cfoE p n m q io il i fo fl)
      (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a
      (fun v ks a' => CfgPost dn vis fe m v.1 v.2 ks a') := by
  cases n with
  | zero => rw [cfoE.eq_1]; exact RefE.of_cls0 (by simp)
  | succ n =>
  rw [cfoE.arm1]
  refine RefE.onlySim (fun _ => rfl) (fun _ _ h => h) fun r1 m1 h1 => ?_
  dsimp only [cfoE.k_block_shape_member_names]
  have hsz := hS.iw.iwSize
  have hf1 := (memberNamesW_dec h1 hsz hS.iw.ctl hb.dec (by have := hb.ptop; have := hS.iw.iw; omega)
    hb.2.1 hb.2.2).2.2.2.1
  obtain ⟨hS1, hg1, -, hd1, ht1⟩ := memberNamesW_stage h1 hS hb
  refine RefE.lastE (fun _ => cfoE.k_class_fields_of_go.none ..) (fun _ => cfoE.k_class_fields_of_go.arm1 ..) id
    (cfg_ref (p := p) bsh ihs n hS1 hd1 (by omega) (hih.grow hg1) hib
      (by rw [decHL_grow hg1 hfb]; exact hfs) (Nat.le_trans hfb hg1.iw) hi (rec2NoMR_iw hf1 hM))
    fun _ _ _ _ hP2 => ⟨hP2.stage, hg1.trans hP2.grow, by simpa using hP2.kinds.mono hg1.iw, hP2.nomr,
      (MFr.of_iw hf1).up.trans hP2.frame, (memberNamesW_afr h1).trans hP2.afr⟩

/-- **`class_fields_of` refines `classFieldsOf`** (through the stub `fvar_type_d`; `cfo_ref`'s ok
half): the fields' kinds are a stable slice of `ClassField` records; `nest_occ`'s memo relation is
needed before and holds after (at some map). -/
@[refines ConRon.Arena.classFieldsOf]
theorem classFieldsOf_refines (hp : CfoProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (q io il i fo fl : Word) (bsh : BlockShape)
    (ihs : List (Nat × Nat)) (fs : List EIdx) (mp0 : Std.HashMap EIdx Bool)
    (hS : StageR dn vis fe s₀.mem a₀) (hb : BSOK s₀.mem q.toNat bsh)
    (hih : StabD (fun m => decPL m (decNN m) io.toNat il.toNat) s₀.mem ihs) (hib : io.toNat + il.toNat < 2 ^ 64)
    (hfs : decHL s₀.mem fo.toNat fl.toNat = some fs) (hfb : fo.toNat + fl.toNat ≤ iwTop s₀.mem)
    (hi : i.toNat + fl.toNat < 2 ^ 64) (hM : noMR s₀.mem mp0) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_fields_of" [q, io, il, i, fo, fl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀ ∧
      CfoQ dn vis fe s₀.mem (r, s'.mem) (AM.st (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀)
        (AM.res (ConRon.Arena.classFieldsOf bsh ihs i.toNat fs) a₀); ⊤⦄ := by
  refine triple_post (RefE.triple (cfoE_spec p hp n s₀ q io il i fo fl)
    (cfo_ref dn vis fe bsh ihs n hS hb hih hib hfs hfb hi hM)) ?_
  rintro r s' ⟨hl, x, a', run, hR⟩
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl, hok, by rw [hst]; exact hR.stage, hR.grow, by rw [hres]; exact hR.kinds, hR.nomr, hR.frame⟩

end cfo

end L.Ind

end
