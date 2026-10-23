import ConAgua.Arena.RecGenSpec20
import ConAgua.Arena.RecGenSpec11
import ConAgua.Arena.IndInstallSpec30

/-!
# `checkBlockClasses` (lane `indproofs4`)

`check_block_classes(vis, p, params.off, params.len, ctorsAs.off, ctorsAs.len)`: `class_read`
(`classRead_refines`, `RecClassSpecH`), its slots' classes (`classReadClasses_refines`,
`RecClassSpec`), the canonical keys (`ckkW_sim`, `RecGenSpec14`), the majors (`clmW_sim`,
`RecGenSpec19`), one class per member (`opmW_ok`).

* **Glue.** `class_read`'s slots are decoded stably (`SPL`); `slots_ok` turns that into the
  decoding and `SlotsExt` that `class_read_classes` takes (`stab_decCS_ext`, `RecGenSpec20`).
  `class_read_classes`' keys (`CcRes`) are decoded below the tops (`ccRes_pslR`: `decCK` reads
  the same in the cut pools for a key whose extent is below the top, `decCK_truncM`).
* **The positivity memos across `class_read` and `class_read_classes`**: neither has a memo
  lemma, so the walk memos (`PosMR`) come from a write-set fact (`hcl`: their closures write no
  stage memo, arrays 201‥208 and `CTL` 202‥219; decided for the checker's program), as the tail's
  `HbMemo.ofClosed`.
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Glue -/

/-- **`class_read`'s stable slots** are decoded with their extents below the top. -/
theorem slots_ok {m : Mem} {so sl : Nat} {slots : List ClassSlot} (h : SPL decCS m so sl slots)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    decPL m (decCS m) so sl = some slots ∧ SlotsExt m so sl := by
  refine ⟨h.decPL, h.1, fun j hj sp hsp => ?_⟩
  obtain ⟨hb, ps, hps, hfa⟩ := h
  have hlen := decNL_length m hps
  have hat := decNL_at hps j hj
  rw [hsp] at hat
  cases hat
  have hl2 := FA2.length_eq hfa
  exact stab_decCS_ext (FA2.get hfa j (by omega) (by omega)) hsz

theorem decCK_truncM {m : Mem} {k : Nat} (hk : CKExt m k) : decCK (truncM m) k = decCK m k := by
  obtain ⟨h1, h2⟩ := hk
  simp only [decCK]
  rw [iwH_truncM (by omega), iwH_truncM (by omega)]
  have hat : decAt (truncM m) (decHL (k := IdxKind.expr) (truncM m)) (k + 2) =
      decAt m (decHL (k := IdxKind.expr) m) (k + 2) := by
    simp only [decAt]
    rw [iwN_truncM (by omega), iwN_truncM (by omega)]
    cases ho : iwN m (k + 2) with
    | none => simp
    | some o =>
      cases hl : iwN m (k + 2 + 1) with
      | none => simp
      | some l =>
        show decHL (truncM m) o l = decHL m o l
        rcases h2 o l ho (by simpa using hl) with hb | rfl
        · exact decHL_truncM hb
        · simp [decHL, hslice?]
  rw [hat]

/-- **`class_read_classes`' keys are decoded below the tops.** -/
theorem ccRes_pslR {m : Mem} {r : List Word} {keys : List ClassKey} (h : CcRes m r keys) :
    PSlR decCK keys (r.headD 0) (r.tail.headD 0) m := by
  obtain ⟨ptrs, hps, hdk, hext, hb⟩ := h
  refine ⟨?_, hb⟩
  show decPL (truncM m) (decCK (truncM m)) _ _ = some keys
  rw [← hdk]
  unfold decPL
  refine mapM_congr_range _ fun j hj => ?_
  have hj' : j < (r.tail.headD 0).toNat := List.mem_range.mp hj
  rw [iwN_truncM (by omega)]
  have hat := decNL_at hps j hj'
  rw [hat]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact decCK_truncM (hext _ (List.getElem_mem _))

/-! ## The model -/

section model
variable (p : Prog) (n : Nat)

/-- After `check_block_classes_one_per_member`: the result. -/
def cbcK5 (rd : Word) (rm : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (g, m) => if g.headD 0 = 0 then none else some ([rd, rm.headD 0, rm.tail.headD 0], m)

/-- After `class_majors`: one class per member. -/
def cbcK4 (pp rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbcK5 rd r (callW p n "check_block_classes_one_per_member"
      [0, rdW (m.arr64 IW) (pp + 1), r.headD 0, r.tail.headD 0] m)

/-- After the keys: the majors. -/
def cbcK3 (vis pp po pl co cl rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbcK4 p n pp rd (callW p n "class_majors"
      [vis, pp, co, cl, po, pl, r.headD 0, r.tail.headD 0] m)

/-- After the classes: the keys. -/
def cbcK2 (vis pp po pl co cl rd : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => cbcK3 p n vis pp po pl co cl rd (callW p n "check_block_classes_keys"
      [rdW (m.arr64 IW) (pp + 4), po, pl, r.headD 0, r.tail.headD 0] m)

/-- After `class_read`: the classes of its slots. -/
def cbcK1 (vis pp po pl co cl : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if r.headD 0 = 0 then none else
      cbcK2 p n vis pp po pl co cl (r.tail.headD 0) (callW p n "class_read_classes"
        [rdW (m.arr64 IW) (r.tail.headD 0), rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m)

/-- **The model of `check_block_classes(vis, p, params.off, params.len, ctorsAs.off,
ctorsAs.len)`** (callees at fuel `n`). -/
def cbcW (m : Mem) (vis pp po pl co cl : Word) : Option (List Word × Mem) :=
  cbcK1 p n vis pp po pl co cl (callW p n "class_read"
    [pp, vis, rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (pp + 2), rdW (m.arr64 IW) (pp + 3)] m)

section arms
variable (vis pp po pl co cl rd : Word) (r rm : List Word) (m : Mem)
theorem cbcK5_some_bad (h : r.headD 0 = 0) : cbcK5 rd rm (some (r, m)) = none := by
  simp only [cbcK5]; rw [if_pos h]
theorem cbcK5_some_ok (h : ¬ r.headD 0 = 0) :
    cbcK5 rd rm (some (r, m)) = some ([rd, rm.headD 0, rm.tail.headD 0], m) := by
  simp only [cbcK5]; rw [if_neg h]
theorem cbcK4_some : cbcK4 p n pp rd (some (r, m)) = cbcK5 rd r (callW p n
    "check_block_classes_one_per_member" [0, rdW (m.arr64 IW) (pp + 1), r.headD 0, r.tail.headD 0] m) := rfl
theorem cbcK3_some : cbcK3 p n vis pp po pl co cl rd (some (r, m)) = cbcK4 p n pp rd (callW p n
    "class_majors" [vis, pp, co, cl, po, pl, r.headD 0, r.tail.headD 0] m) := rfl
theorem cbcK2_some : cbcK2 p n vis pp po pl co cl rd (some (r, m)) = cbcK3 p n vis pp po pl co cl rd
    (callW p n "check_block_classes_keys" [rdW (m.arr64 IW) (pp + 4), po, pl, r.headD 0, r.tail.headD 0] m) :=
  rfl
theorem cbcK1_some_bad (h : r.headD 0 = 0) : cbcK1 p n vis pp po pl co cl (some (r, m)) = none := by
  simp only [cbcK1]; rw [if_pos h]
theorem cbcK1_some_ok (h : ¬ r.headD 0 = 0) : cbcK1 p n vis pp po pl co cl (some (r, m)) =
    cbcK2 p n vis pp po pl co cl (r.tail.headD 0) (callW p n "class_read_classes"
      [rdW (m.arr64 IW) (r.tail.headD 0), rdW (m.arr64 IW) (r.tail.headD 0 + 1)] m) := by
  simp only [cbcK1]; rw [if_neg h]
end arms

end model

attribute [ind_grind] cbcK5_some_bad cbcK5_some_ok cbcK4_some cbcK3_some cbcK2_some cbcK1_some_bad
  cbcK1_some_ok

set_option maxHeartbeats 1600000 in
theorem cbc_spec (p : Prog) (hp : p.lookup "check_block_classes" = some checkBlockClassesL) (n : Nat)
    (s₀ : St) (vis pp po pl co cl : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_classes" [vis, pp, po, pl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ cbcW p n s₀.mem vis pp po pl co cl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockClassesL]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "class_read", callW_spec p n "class_read_classes",
      callW_spec p n "check_block_classes_keys", callW_spec p n "class_majors",
      callW_spec p n "check_block_classes_one_per_member"] <;>
    finish (gen := 40) (instances := 20000) [cbcW, rdW_eq]

/-! ## The relation -/

/-- The lookups of `check_block_classes`. -/
structure CbcProg (p : Prog) : Prop where
  read : ReadProg p
  clm : ClmProg p
  ha : p.lookup "iw_alloc" = some iwAlloc
  crc : p.lookup "class_read_classes" = some classReadClasses
  cnt : p.lookup "check_block_classes_count" = some checkBlockClassesCount
  opm : p.lookup "check_block_classes_one_per_member" = some checkBlockClassesOnePerMember
  cbc : p.lookup "check_block_classes" = some checkBlockClassesL

/-- **`check_block_classes`' model refines `checkBlockClasses`.** -/
theorem cbcW_sim {p : Prog} (hP : CbcProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfr : "class_read" ∈ fs)
    (hfc : "class_read_classes" ∈ fs) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (hcs : CtorSums fe) (n : Nat) (hn : 2 ^ 31 + n ≤ coreWalkFuel) (m : Mem) (a : AState)
    (pp po pl co cl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (hS : StageR dn vis fe m a) (hb : BSOK m pp.toNat bs) (hsrc : ShapeSrc m pp)
    (hrecs : RecsDec m (rdW (m.arr64 IW) (pp + 2)) (rdW (m.arr64 IW) (pp + 3)) bs.recs)
    (hcss : PSlR decCNS css co cl m) (hpf : DecB (fun m => decHL m po.toNat pl.toNat) m pfvs)
    (hpfb : po.toNat + pl.toNat ≤ iwTop m) (hPm : PosMR m) :
    Sim (cbcW p n m vis pp po pl co cl) (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧
        StabD (fun m => decCR m (r.headD 0).toNat) m' x.1 ∧
        PSlR decTM x.2 (r.tail.headD 0) (r.tail.tail.headD 0) m' ∧ PosMR m') := by
  intro r m' h
  have hbsD : DecB (fun m => decBS m pp.toNat) m bs := hb.1
  obtain ⟨-, hq9, -⟩ := partsShapeFacts hbsD hsrc
  obtain ⟨hnp, hnpb, -, -⟩ := partsShapeWords (IWGrow.refl m) hbsD hq9
  have hnpT : (UInt64.ofNat bs.nP : Word).toNat = bs.nP := UInt64.toNat_ofNat_of_lt' hnpb
  unfold cbcW at h
  -- `class_read`
  cases c1 : callW p n "class_read" [pp, vis, rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (pp + 2),
      rdW (m.arr64 IW) (pp + 3)] m with
  | none => rw [c1] at h; cases h
  | some q1 =>
  obtain ⟨r1, m1⟩ := q1
  rw [c1] at h
  obtain ⟨s1, hs1, -, hok1, hS1, hg1, hd1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (classRead_refines p hP.read n _ a dn vis fe pp _ _ _ bs bs.recs hS hb hrecs) c1
  simp only at hs1 hS1 hg1 hd1
  subst hs1
  have hP1 := PosMR.ofClosed hcl hfr c1 hPm
  rw [hnp, hnpT] at hok1 hS1 hd1
  have hrun1 := AM.run_of_ok _ a hok1
  generalize hx1 : AM.res (ConRon.Arena.classRead bs fe bs.nP bs.recs) a = x1 at hrun1 hd1
  generalize ha1 : AM.st (ConRon.Arena.classRead bs fe bs.nP bs.recs) a = a1 at hrun1 hS1
  cases x1 with
  | none =>
    simp only [decRead] at hd1
    rw [cbcK1_some_bad p n vis pp po pl co cl r1 s1.mem hd1] at h; cases h
  | some rd =>
  obtain ⟨h1ok, hrdS, so, sl, hso, hsl, hspl⟩ := hd1
  have h1ne : ¬ r1.headD 0 = 0 := by rw [h1ok]; decide
  rw [cbcK1_some_ok p n vis pp po pl co cl r1 s1.mem h1ne] at h
  have hsz1 : (s1.mem.arr64 IW).size < 2 ^ 64 := hS1.2.2.2.1
  obtain ⟨wso, hwsob⟩ := iwN_rdW_at (k := 0) (w := r1.tail.headD 0) (by simpa using hso) hsz1
  obtain ⟨wsl, hwslb⟩ := iwN_rdW_at (k := 1) (w := r1.tail.headD 0) hsl hsz1
  rw [show (r1.tail.headD 0 + UInt64.ofNat 0 : Word) = r1.tail.headD 0 by simp] at wso
  rw [show (UInt64.ofNat 1 : Word) = 1 from rfl] at wsl
  rw [wso, wsl] at h
  have hsoT : (UInt64.ofNat so : Word).toNat = so := UInt64.toNat_ofNat_of_lt' hwsob
  have hslT : (UInt64.ofNat sl : Word).toNat = sl := UInt64.toNat_ofNat_of_lt' hwslb
  obtain ⟨hslots, hext⟩ := slots_ok hspl hsz1
  -- `class_read_classes`
  cases c2 : callW p n "class_read_classes" [UInt64.ofNat so, UInt64.ofNat sl] s1.mem with
  | none => rw [c2] at h; cases h
  | some q2 =>
  obtain ⟨r2, m2⟩ := q2
  rw [c2, cbcK2_some] at h
  obtain ⟨s2, hs2, -, hS2, hg2, hcc⟩ := triple_of_callW (s₀ := ⟨s1.mem, Locals.init []⟩)
    (classReadClasses_refines p hP.clm.keys.copy hP.ha hP.clm.keys.cons hP.crc n _ a1 dn vis fe
      (UInt64.ofNat so) (UInt64.ofNat sl) rd.slots hS1 (by rw [hsoT, hslT]; exact hslots)
      (by rw [hsoT, hslT]; exact hext)) c2
  simp only at hs2 hS2 hg2 hcc
  subst hs2
  have hP2 := PosMR.ofClosed hcl hfc c2 hP1
  have hg02 := hg1.trans hg2
  -- the keys
  obtain ⟨hnp2, -, -, -⟩ := partsShapeWords hg02 hbsD hq9
  rw [hnp2] at h
  cases c3 : callW p n "check_block_classes_keys" [UInt64.ofNat bs.nP, po, pl, r2.headD 0,
      r2.tail.headD 0] s2.mem with
  | none => rw [c3] at h; cases h
  | some q3 =>
  obtain ⟨r3, m3⟩ := q3
  rw [c3, cbcK3_some] at h
  obtain ⟨s3, hs3, -, hW3⟩ := triple_of_callW (s₀ := ⟨s2.mem, Locals.init []⟩)
    (ckk_spec p hP.clm.keys.keys n _ (UInt64.ofNat bs.nP) po pl (r2.headD 0) (r2.tail.headD 0)) c3
  simp only at hs3 hW3
  subst hs3
  obtain ⟨keys, a3, hrun3, hS3, hg3, hks, hP3⟩ :=
    ckkW_sim hP.clm.keys dn vis fe (UInt64.ofNat bs.nP) po pl pfvs n hn s2.mem a1 _ _ _ hS2
      (hpf.grow (OMono.decHL _ _) hg02) (Nat.le_trans hpfb hg02.1) (ccRes_pslR hcc) hP2 r3 s3.mem hW3
  rw [hnpT] at hrun3
  have hg03 := hg02.trans hg3
  -- the majors
  cases c4 : callW p n "class_majors" [vis, pp, co, cl, po, pl, r3.headD 0, r3.tail.headD 0] s3.mem with
  | none => rw [c4] at h; cases h
  | some q4 =>
  obtain ⟨r4, m4⟩ := q4
  rw [c4, cbcK4_some] at h
  obtain ⟨s4, hs4, -, hW4⟩ := triple_of_callW (s₀ := ⟨s3.mem, Locals.init []⟩)
    (clm_spec p hP.clm.cm n _ vis pp co cl po pl (r3.headD 0) (r3.tail.headD 0)) c4
  simp only at hs4 hW4
  subst hs4
  obtain ⟨ms, a4, hrun4, hS4, hg4, hms, hP4⟩ :=
    clmW_sim hP.clm dn vis fe hcs pp co cl po pl bs css pfvs n hn s3.mem a3 _ _ keys hS3
      (hbsD.grow (decBS_mono _) hg03) (partsHsrc_grow hg03 hq9 hsrc) (hcss.grow decCNS_mono hg03)
      (hpf.grow (OMono.decHL _ _) hg03) (Nat.le_trans hpfb hg03.1) hks hP3 r4 s4.mem hW4
  have hg04 := hg03.trans hg4
  -- one class per member
  cases c5 : callW p n "check_block_classes_one_per_member"
      [0, rdW (s4.mem.arr64 IW) (pp + 1), r4.headD 0, r4.tail.headD 0] s4.mem with
  | none => rw [c5] at h; cases h
  | some q5 =>
  obtain ⟨r5, m5⟩ := q5
  rw [c5] at h
  obtain ⟨s5, hs5, -, hm5, hW5⟩ := triple_of_callW (s₀ := ⟨s4.mem, Locals.init []⟩)
    (opm_spec p hP.cnt hP.opm n _ 0 (rdW (s4.mem.arr64 IW) (pp + 1)) (r4.headD 0) (r4.tail.headD 0)) c5
  simp only at hs5 hm5 hW5
  subst hs5
  have hT0 : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hpp1 : pp.toNat + 1 < 2 ^ 64 := by omega
  have hq1 : (pp + 1 : Word).toNat = pp.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hk1 : rdW (s4.mem.arr64 IW) (pp + 1) = UInt64.ofNat bs.k := by
    rw [partsRdIW_grow hg04 (by rw [hq1]; omega)]
    have e : (pp + 1 : Word) = UInt64.ofNat (pp.toNat + 1) := by
      apply UInt64.toNat_inj.mp; rw [hq1]; simp; omega
    rw [e]; exact decBS_k (hbsD.get (decBS_mono _)) hpp1
  have hsz4 : (s4.mem.arr64 IW).size < 2 ^ 64 := hS4.2.2.2.1
  have hgood := opmW_ok n s4.mem 0 _ _ _ _ ms hW5 (hms.1.get (OMono.decPL (fun q => decTM_mono q) _ _))
    (by have := hms.2; have := Nat.lt_of_le_of_lt hS4.2.1 hsz4; omega) hsz4
  obtain ⟨ok, lk, -, hlk, hgdk⟩ := decAt_some (decBS_some (hbsD.get (decBS_mono _))).1
  have hkb : bs.k < 2 ^ 64 := by rw [BlockShape.k, decPL_length _ hgdk]; exact (iwN_rdW hlk hpp1).2
  rw [hk1, UInt64.toNat_ofNat_of_lt' hkb, show (0 : Word).toNat = 0 from rfl, Nat.sub_zero,
    ← List.range_eq_range'] at hgood
  by_cases hz : r5.headD 0 = 0
  · rw [cbcK5_some_bad _ _ _ _ hz] at h; cases h
  rw [cbcK5_some_ok _ _ _ _ hz] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hall : (List.range bs.k).all (fun t => (ms.filter (·.member == some t)).length == 1) = true := by
    have : (r5.headD 0 != 0) = true := by simpa using hz
    rw [this] at hgood; exact hgood.symm
  rw [hm5]
  refine ⟨(rd, ms), a4, ?_, hS4, hg04, ?_, by simpa using hms, hP4⟩
  · simp only [ConRon.Arena.checkBlockClasses, StateT.run_bind, hrun1, except_ok_bind]
    simp only [hrun3, except_ok_bind, hrun4, hall, if_true]
    rfl
  · simpa using hrdS.grow (hg2.trans (hg3.trans hg4))

/-- **`check_block_classes` refines `checkBlockClasses`**: from the stage relation, the shape
(`BSOK`, its slice bound `ShapeSrc`, its recursors decoded with word-sized major indices), the
constructors and parameters decoded below the tops and the walk memos well formed, the class
reading at `r[0]` (decoded stably) and the classes' majors at `(r[1], r[2])` (below the tops), the
memos kept. Program facts: the lookups (`CbcProg`) and the write set of `class_read`,
`class_read_classes` (`hcl`, as `check_block_tail`'s). -/
@[refines ConRon.Arena.checkBlockClasses]
theorem checkBlockClasses_refines {p : Prog} (hP : CbcProg p) {fs : List FnName}
    (hcl : closedA p posFreeA posFreeC fs = true) (hfr : "class_read" ∈ fs)
    (hfc : "class_read_classes" ∈ fs) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (hcs : CtorSums fe) (n : Nat) (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState)
    (pp po pl co cl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (hS : StageR dn vis fe s₀.mem a₀) (hb : BSOK s₀.mem pp.toNat bs)
    (hsrc : ShapeSrc s₀.mem pp)
    (hrecs : RecsDec s₀.mem (rdW (s₀.mem.arr64 IW) (pp + 2)) (rdW (s₀.mem.arr64 IW) (pp + 3)) bs.recs)
    (hcss : PSlR decCNS css co cl s₀.mem) (hpf : DecB (fun m => decHL m po.toNat pl.toNat) s₀.mem pfvs)
    (hpfb : po.toNat + pl.toNat ≤ iwTop s₀.mem) (hPm : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p (n + 1)) "check_block_classes" [vis, pp, po, pl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀) ∧
      IWGrow s₀.mem s'.mem ∧
      StabD (fun m => decCR m (r.headD 0).toNat) s'.mem
        (AM.res (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀).1 ∧
      PSlR decTM (AM.res (ConRon.Arena.checkBlockClasses V fe bs pfvs css) a₀).2
        (r.tail.headD 0) (r.tail.tail.headD 0) s'.mem ∧ PosMR s'.mem; ⊤⦄ :=
  triple_post (cbc_spec p hP.cbc n s₀ vis pp po pl co cl) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (cbcW_sim hP hcl hfr hfc dn vis fe hcs n hn _ a₀ pp po pl co cl bs css pfvs
      hS hb hsrc hrecs hcss hpf hpfb hPm) hm
    ⟨hl, hok, hQ⟩

end L.Ind
