import ConAgua.Arena.IndInstallSpec30

/-!
# Refinements of `IndInstall`, part 31 (lane `indproofs3`, helper `tail`): `checkBlockTail`, the
relation

`ictlW_sim`: the tail's model refines `checkBlockTail` from the pass's record (`BPassR`), the
stage relation at its environment, the raw block decoded, and the `hb` memo well formed.

**Pending (no census tag yet):** `cons_block_recs_tf` enters as `ConsRecsTFSim p`, the `Sim` fact
the tail needs of it, an argument until helper `indproofs3-rec`'s refinement of `consBlockRecsTF`
lands (then it is that theorem). `check_block_rec` enters through `checkBlockRec_refines` as it is
(today through `genRecCheck_pending`).

**Hypotheses beyond the stage relation and the decodings** (each the caller's):
* `HbMemo m` (for the projection tables' `struct_proj_guards`), returned for the memory after;
* `closedA p hbFreeA hbFreeC fs` with the six callees in `fs` (a program fact: `decide +kernel` at
  `checkerProg`), so that the callees with no memo lemma keep the `hb` memo;
* the fuel bound `2 ^ 31 + n ≤ coreWalkFuel` (the tables').
-/

set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-- **What the tail needs of `cons_block_recs_tf(vis2, p, 0, out.off, out.len, vis)`**: from the
stage relation at `vis` of `fe`, the shape and the recursor stage's output decoded below the tops,
and the `hb` memo, a returning run is `consBlockRecsTF` at the view `vis2`. (To be discharged by
helper `indproofs3-rec`'s refinement.) -/
def ConsRecsTFSim (p : Prog) : Prop :=
  ∀ (n : Nat) (dn : NIdx → Option ConLeche.Name) (vis vis2 pp : Word) (fe : IFEnv) (m : Mem) (a : AState)
    (bs : BlockShape) (rr : List Word) (outs : List (IConstantVal × TargetMajor × List EIdx)),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → decRRS m rr outs → HbMemo m → AbsOK m →
    Sim (callW p n "cons_block_recs_tf" [vis2, pp, 0, rr.headD 0, rr.tail.headD 0, vis] m)
      (ConRon.Arena.consBlockRecsTF vis2.toNat bs 0 outs fe) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m')

/-- Replace the model by one that returns whatever it returns. -/
theorem Sim.of_model {β α : Type} {mo mo' : Option (β × Mem)} {op : AM α} {a : AState}
    {Q : β → α → Mem → AState → Prop} (h : ∀ r m', mo = some (r, m') → mo' = some (r, m'))
    (hs : Sim mo' op a Q) : Sim mo op a Q := fun r m' e => hs r m' (h r m' e)

/-- The lookups of `check_block_tail`. -/
structure TailProg (p : Prog) : Prop where
  idx : IdxProg p
  recp : RecProg p
  hci : p.lookup "ctor_info_rec" = some ctorInfoRecL
  hcs : p.lookup "cons_sum_ctors" = some consSumCtorsL
  hcbc : p.lookup "cons_block_ctors" = some consBlockCtors
  flush : FlushProg p
  nf : p.lookup "nest_field_kind_flat" = some nestFieldKindFlat
  ni : p.lookup "nest_kinds_flat_inner" = some nestKindsFlatInner
  nm : p.lookup "nest_kinds_flat_mid" = some nestKindsFlatMid
  nk : p.lookup "nest_kinds_flat" = some nestKindsFlat
  ng : p.lookup "block_nested_bit_go" = some blockNestedBitGo
  nb : p.lookup "block_nested_bit" = some blockNestedBit
  crec : p.lookup "check_block_rec" = some checkBlockRec
  tailrec : p.lookup "check_block_tail_rec" = some checkBlockTailRec
  tabs : TabsProg p
  tail : p.lookup "check_block_tail" = some checkBlockTail

/-- The tail's callees with no memo lemma. -/
def tailCallees : List FnName :=
  ["check_block_idx_sorts", "cons_block_ctors", "block_nested_bit", "check_block_rec", "cons_block_recs_tf"]

/-- **The pass's record at `q`**: decoded below the tops at `fe` (whose view `vis` is word 0), its
slices and the shape's members below the top. -/
def BPassR (vis : Word) (fe : IFEnv) (m : Mem) (q : Word) (bp : BlockPass) : Prop :=
  DecB (fun m => decBPass fe m q.toNat) m bp ∧ BPassB m q.toNat ∧ rdW (m.arr64 IW) q = vis ∧
    ShapeSrc m (rdW (m.arr64 IW) (q + 3))

theorem tailToNat {q : Word} {k : Nat} (h : q.toNat + k < 2 ^ 64) :
    (q + UInt64.ofNat k).toNat = q.toNat + k := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega)]; exact Nat.mod_eq_of_lt h

/-- The tail's callees outside the `abstract1` cascade, which keep its memo (`AbsKeep`, a program
fact). -/
def tailKeepCallees : List FnName :=
  ["check_block_idx_sorts", "cons_block_ctors", "check_block_rec", "check_block_tables"]

/-- **`check_block_tail`'s model refines `checkBlockTail`.** -/
theorem ictlW_sim {p : Prog} (hP : TailProg p) (hRecs : ConsRecsTFSim p) {fs : List FnName}
    (hfs : ∀ f ∈ tailCallees, f ∈ fs) (hcl : closedA p hbFreeA hbFreeC fs = true) (n : Nat)
    (hn : 2 ^ 31 + n ≤ coreWalkFuel) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {m : Mem} {a : AState} {bO bL q : Word} {bp : BlockPass} {block : List IConstantInfo}
    (hS : StageR dn vis fe m a) (hq : BPassR vis fe m q bp)
    (hblk : DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m block) (hM : HbMemo m) (hA : AbsOK m)
    (hkeep : ∀ f ∈ tailKeepCallees, AbsKeep p f) :
    Sim (ictlW p n m bO bL q) (ConRon.Arena.checkBlockTail V block bp) a
      (fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m m' ∧ HbMemo m' ∧ AbsOK m') := by
  obtain ⟨hdq, hB, hw0, hsrc⟩ := hq
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hq19 := hB.1
  have hk : ∀ k, k < 19 → (q + UInt64.ofNat k).toNat = q.toNat + k := fun k hk => tailToNat (by omega)
  -- the record
  have hdq' : decBPass fe (truncM m) q.toNat = some bp := hdq
  simp only [decBPass, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdq'
  obtain ⟨cvTas, hcv, pw, hpw, bs, hbs, ctorsAs, hca, sss, hsss, kinds, hkd, nfs, hnfs, params, hpar, rdp,
    hrdp, rd, hrd, cls, hcls, tbl, htbl, rfl⟩ := hdq'
  obtain ⟨hw3, hpwb⟩ := bpWord hpw (hk 3 (by decide))
  rw [show (q + UInt64.ofNat 3 : Word) = q + 3 from rfl] at hw3
  rw [hw3] at hsrc
  have hpw' : (UInt64.ofNat pw : Word).toNat = pw := UInt64.toNat_ofNat_of_lt' hpwb
  have hbsD : DecB (fun m => decBS m (UInt64.ofNat pw : Word).toNat) m bs := by rw [hpw']; exact hbs
  obtain ⟨hmem, -, -, -, -, -, -⟩ := decBS_some hbs
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hbsD hsrc
  have hpw9 : pw + 9 ≤ iwTop m := by rw [← hpw']; exact hq9
  -- the slices
  have hmss := bpPSl decMS_mono hmem (fun o l h1 h2 => hsrc o l (by rw [hpw']; exact h1) (by rw [hpw']; exact h2))
    (w := UInt64.ofNat pw) (w1 := UInt64.ofNat pw + 1) hpw'
    (by rw [UInt64.toNat_add, hpw']; simp; omega)
  have e : ∀ k : Nat, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → w.toNat = q.toNat + k :=
    fun k hk w hw => by rw [hw]; exact tailToNat (by omega)
  have hcvs := bpPSl (fun q => OMono.decCVp q) hcv (hB.2 1 (by simp)) (w := q + 1) (w1 := q + 2)
    (e 1 (by decide) _ rfl) (e 2 (by decide) _ rfl)
  have hcas := bpPSl decCNS_mono hca (hB.2 4 (by simp)) (w := q + 4) (w1 := q + 5)
    (e 4 (by decide) _ rfl) (e 5 (by decide) _ rfl)
  have hsss' := bpPSl decISS_mono hsss (hB.2 6 (by simp)) (w := q + 6) (w1 := q + 7)
    (e 6 (by decide) _ rfl) (e 7 (by decide) _ rfl)
  have hkfm : ∀ q, OMono (fun m => decLH m (decPL m (decLH m (decKL m))) q) :=
    fun q => OMono.decAt (fun o l => OMono.decPL (fun q => OMono.decAt (fun o l => decKL_mono o l) q) o l) q
  have hks := bpPSl hkfm hkd (hB.2 8 (by simp)) (w := q + 8) (w1 := q + 9)
    (e 8 (by decide) _ rfl) (e 9 (by decide) _ rfl)
  obtain ⟨hpd, hpb⟩ := bpHSl hpar (hB.2 12 (by simp)) (w := q + 12) (w1 := q + 13)
    (e 12 (by decide) _ rfl) (e 13 (by decide) _ rfl)
  obtain ⟨hw14, hrdb⟩ := bpWord hrdp (e 14 (by decide) _ rfl)
  have hrdD : DecB (fun m => decCR m (UInt64.ofNat rdp : Word).toNat) m rd := by
    rw [UInt64.toNat_ofNat_of_lt' hrdb]; exact hrd
  have hcls' := bpPSl (fun q => decTM_mono q) hcls (hB.2 15 (by simp)) (w := q + 15) (w1 := q + 16)
    (e 15 (by decide) _ rfl) (e 16 (by decide) _ rfl)
  have htbl' := bpPSl (fun q => decNCN_mono q) htbl (hB.2 17 (by simp)) (w := q + 17) (w1 := q + 18)
    (e 17 (by decide) _ rfl) (e 18 (by decide) _ rfl)
  -- `check_block_idx_sorts`
  unfold ictlW
  rw [hw0, hw3]
  unfold ConRon.Arena.checkBlockTail
  refine Sim.bindK (K := ictlK1 p n bO bL q (UInt64.ofNat pw) vis) rfl (fun _ _ => rfl)
    (Q := fun _ _ m1 a1 => StageR dn vis fe m1 a1 ∧ IWGrow m m1 ∧ HbMemo m1 ∧ AbsOK m1)
    (fun r m1 e1 => by
      obtain ⟨s1, rfl, -, hok, hS1, hg1, -⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
        (checkBlockIdxSorts_refines p hP.idx n _ a dn vis fe _ _ _ _ _ bs bs.members cvTas hS hbsD hsrc hmss hcvs) e1
      exact ⟨_, _, partsRunOfOk hok, hS1, hg1, HbMemo.ofClosed hcl (hfs _ (by decide)) e1 hM,
        hkeep _ (by simp [tailKeepCallees]) _ _ _ _ _ e1 hA⟩) ?_
  rintro r1 - m1 a1 ⟨hS1, hg1, hM1, hA1⟩
  rw [ictlK1_some]
  -- `cons_block_ctors` (the twin's `fe₂`, a pure function)
  obtain ⟨hnp1, -, -, -⟩ := partsShapeWords hg1 hbsD hq9
  have hca1 := hcas.grow decCNS_mono hg1
  refine Sim.mstep (K := ictlK2 p n bO bL q (UInt64.ofNat pw)) rfl (fun _ _ => rfl) fun r2 m2 h2 => ?_
  rw [partsRdIW_grow hg1 (w := q + 4) (by rw [e 4 (by decide) (q + 4) rfl]; omega),
    partsRdIW_grow hg1 (w := q + 5) (by rw [e 5 (by decide) (q + 5) rfl]; omega)] at h2
  rw [hnp1] at h2
  obtain ⟨s2, rfl, -, hS2, hg2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
    (consBlockCtors_refines p hP.recp hP.hci hP.hcs hP.hcbc n _ a1 dn fe _ _ _ vis ctorsAs hS1 hca1) h2
  have hM2 : HbMemo s2.mem := HbMemo.ofClosed hcl (hfs _ (by decide)) h2 hM1
  have hA2 : AbsOK s2.mem := hkeep _ (by simp [tailKeepCallees]) _ _ _ _ _ h2 hA1
  rw [UInt64.toNat_ofNat_of_lt' (partsShapeWords (IWGrow.refl m) hbsD hq9).2.1] at hS2
  rw [ictlK2_some]
  -- the flush
  dsimp only
  refine Sim.bindK (K := ictlK3 p n bO bL q (UInt64.ofNat pw) (r2.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withFr (F := AbsOK) (tailSimFlush hP.flush n hS2 hM2) (fun _ _ e => by
      obtain ⟨s', rfl, -, -, hmem⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩) (flushCaches_spec p hP.flush n _) e
      rw [hmem]; exact AFr.of_frame (flushMem_frame _) (by decide) (by decide) hA2)) ?_
  rintro - - m3 a3 ⟨⟨hS3, hg3, hM3⟩, hA3⟩
  rw [ictlK3_some]
  have hg03 := (hg1.trans hg2).trans hg3
  -- `block_nested_bit` (the twin's `nested`, a pure function)
  refine Sim.mstep (K := ictlK4 p n bO bL q (UInt64.ofNat pw) (r2.headD 0)) rfl (fun _ _ => rfl) fun r4 m4 h4 => ?_
  have hks3 := hks.grow hkfm hg03
  rw [partsRdIW_grow hg03 (w := q + 8) (by rw [e 8 (by decide) (q + 8) rfl]; omega),
    partsRdIW_grow hg03 (w := q + 9) (by rw [e 9 (by decide) (q + 9) rfl]; omega)] at h4
  obtain ⟨s4, rfl, hs4, hr4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
    (blockNestedBit_refines p hP.nf hP.ni hP.nm hP.nk hP.ng hP.nb n _ _ _ _ bs kinds hS3.2.2.2.1
      (DecB.get (decBS_mono _) (hbsD.grow (decBS_mono _) hg03)) (DecB.get (OMono.decPL hkfm _ _) hks3.1)) h4
  subst hs4
  have hnb : (r4.headD 0 != 0) = ConRon.Arena.blockNestedBit bs kinds := by
    rw [hr4]; cases ConRon.Arena.blockNestedBit bs kinds <;> rfl
  -- `check_block_rec`
  have hrd3 : rdW (m3.arr64 IW) (q + 14) = UInt64.ofNat rdp := by
    rw [partsRdIW_grow hg03 (w := q + 14) (by rw [e 14 (by decide) (q + 14) rfl]; omega)]; exact hw14
  have hpre : DecB (fun m => decBS m (UInt64.ofNat pw : Word).toNat) m3 bs ∧
      decHL m3 (rdW (m3.arr64 IW) (q + 12)).toNat (rdW (m3.arr64 IW) (q + 13)).toNat = some params ∧
      (rdW (m3.arr64 IW) (q + 12)).toNat + (rdW (m3.arr64 IW) (q + 13)).toNat ≤ iwTop m3 ∧
      PSlR decNCN tbl (rdW (m3.arr64 IW) (q + 17)) (rdW (m3.arr64 IW) (q + 18)) m3 ∧
      DecB (fun m => decCR m (rdW (m3.arr64 IW) (q + 14)).toNat) m3 rd ∧
      PSlR decTM cls (rdW (m3.arr64 IW) (q + 15)) (rdW (m3.arr64 IW) (q + 16)) m3 ∧
      PSlR decCVp cvTas (rdW (m3.arr64 IW) (q + 1)) (rdW (m3.arr64 IW) (q + 2)) m3 ∧
      DecB (fun m => decEBlk dn m bO.toNat bL.toNat) m3 block := by
    have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m3.arr64 IW) w = rdW (m.arr64 IW) w :=
      fun k hk w hw => partsRdIW_grow hg03 (by rw [e k hk w hw]; omega)
    refine ⟨hbsD.grow (decBS_mono _) hg03, ?_, ?_, ?_, ?_, ?_, ?_, hblk.grow ?_ hg03⟩
    · rw [r 12 (by decide) (q + 12) rfl, r 13 (by decide) (q + 13) rfl]; exact (by rw [decHL_grow3 hg03 hpb]; exact hpd)
    · rw [r 12 (by decide) (q + 12) rfl, r 13 (by decide) (q + 13) rfl]; exact Nat.le_trans hpb hg03.1
    · rw [r 17 (by decide) (q + 17) rfl, r 18 (by decide) (q + 18) rfl]; exact htbl'.grow (fun q => decNCN_mono q) hg03
    · rw [hrd3]; exact hrdD.grow (decCR_mono _) hg03
    · rw [r 15 (by decide) (q + 15) rfl, r 16 (by decide) (q + 16) rfl]; exact hcls'.grow (fun q => decTM_mono q) hg03
    · rw [r 1 (by decide) (q + 1) rfl, r 2 (by decide) (q + 2) rfl]; exact hcvs.grow (fun q => OMono.decCVp q) hg03
    · exact decEBlk_mono _ _ _
  -- through `check_block_tail_rec`
  rw [ictlK4_some]
  refine Sim.post (K := ictlK7) rfl (fun _ _ => rfl) ?_ (fun r x m' a' h => h)
  cases n with
  | zero => rw [callW_zero]; exact Sim.of_none
  | succ k =>
  refine Sim.of_model (mo' := ictrW p k m3 bO bL q (UInt64.ofNat pw) (r2.headD 0) (r4.headD 0))
    (fun r m' e => ?_) ?_
  · obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (ictr_spec p hP.tailrec k _ bO bL q (UInt64.ofNat pw) (r2.headD 0) (r4.headD 0)) e
    exact hW
  unfold ictrW
  have hrec : Sim (callW p k "check_block_rec" [r2.headD 0, UInt64.ofNat pw, r4.headD 0,
        rdW (m3.arr64 IW) (q + 12), rdW (m3.arr64 IW) (q + 13), rdW (m3.arr64 IW) (q + 17),
        rdW (m3.arr64 IW) (q + 18), rdW (m3.arr64 IW) (q + 14), rdW (m3.arr64 IW) (q + 15),
        rdW (m3.arr64 IW) (q + 16), bO, bL, rdW (m3.arr64 IW) (q + 1), rdW (m3.arr64 IW) (q + 2)] m3)
      (ConRon.Arena.checkBlockRec V (ConRon.Arena.consBlockCtors bs.nP ctorsAs fe) ⟨bs⟩ (ConRon.Arena.blockNestedBit bs kinds) params tbl rd
        cls block cvTas) a3
      (fun r x m' a' => (StageR dn (r.headD 0) x.1 m' a' ∧ IWGrow m3 m' ∧ decRRS m' r.tail x.2) ∧ HbMemo m') := by
    refine Sim.withFr (Sim.callW_pos (fun j => installSimCall
      (checkBlockRec_refines p hP.crec j ⟨m3, Locals.init []⟩ a3 dn _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs params tbl rd
        cls cvTas block hS3 hpre) (fun r s' h => by obtain ⟨-, hok, hS', hg, hd⟩ := h; rw [hnb] at hok hS' hd; exact ⟨hok, hS', hg, hd⟩)) k)
      (fun r m' e5 => HbMemo.ofClosed hcl (hfs _ (by decide)) e5 hM3)
  refine Sim.bindK (K := ictrK5 p k q (UInt64.ofNat pw) (r2.headD 0)) rfl (fun _ _ => rfl)
    (Sim.withFr hrec (fun _ _ e5 => hkeep _ (by simp [tailKeepCallees]) _ _ _ _ _ e5 hA3)) ?_
  rintro r5 ⟨fe2b, outs⟩ m5 a5 ⟨⟨⟨hS5, hg5, hd5⟩, hM5⟩, hA5⟩
  dsimp only
  rw [ictrK5_some, hS2.1.env.vis]
  -- `cons_block_recs_tf`
  refine Sim.bindK (K := ictrK6 p k q (UInt64.ofNat pw))
    rfl (fun _ _ => rfl)
    (hRecs k dn (r5.headD 0) (r2.headD 0) (UInt64.ofNat pw) fe2b m5 a5 bs r5.tail outs hS5
      ((hbsD.grow (decBS_mono _) hg03).grow (decBS_mono _) hg5) hd5 hM5 hA5) ?_
  rintro r6 fe3 m6 a6 ⟨hS6, hg6, hM6, hA6⟩
  rw [ictrK6_some]
  -- `check_block_tables`
  have hg06 := (hg03.trans hg5).trans hg6
  have r : ∀ k, k < 19 → ∀ w : Word, w = q + UInt64.ofNat k → rdW (m6.arr64 IW) w = rdW (m.arr64 IW) w :=
    fun k hk w hw => partsRdIW_grow hg06 (by rw [e k hk w hw]; omega)
  rw [partsRdIW_grow hg06 (w := UInt64.ofNat pw) (by rw [hpw']; omega),
    partsRdIW_grow hg06 (w := UInt64.ofNat pw + 1) (by rw [UInt64.toNat_add, hpw']; simp; omega),
    r 4 (by decide) (q + 4) rfl, r 5 (by decide) (q + 5) rfl, r 6 (by decide) (q + 6) rfl,
    r 7 (by decide) (q + 7) rfl]
  refine Sim.post (K := ictlK7) rfl (fun _ _ => rfl)
    (Q := fun r x m' a' => StageR dn (r.headD 0) x m' a' ∧ IWGrow m6 m' ∧ HbMemo m' ∧ AbsOK m')
    (fun r m' e7 => by
      have hA7 := hkeep _ (by simp [tailKeepCallees]) _ _ _ _ _ e7 hA6
      obtain ⟨s7, rfl, -, hW7⟩ := triple_of_callW (s₀ := ⟨m6, Locals.init []⟩)
        (ctb_spec p hP.tabs.tabs k _ _ _ _ _ _ _ _ _) e7
      obtain ⟨x, a', h1, h2, h3, h4⟩ := ctbW_sim hP.tabs dn (UInt64.ofNat pw) bs k m6 a6 (r6.headD 0) fe3 _ _ _ _ _
        _ bs.members ctorsAs sss
        (by omega) hS6 ((hbsD.grow (decBS_mono _) hg06)) (partsHsrc_grow hg06 hq9 hsrc) (hmss.grow decMS_mono hg06)
        (hcas.grow decCNS_mono hg06) (hsss'.grow decISS_mono hg06) hM6 r s7.mem hW7
      exact ⟨x, a', h1, h2, h3, h4, hA7⟩)
    (fun r x m7 a7 h => ⟨h.1, hg06.trans h.2.1, h.2.2⟩)

end L.Ind
