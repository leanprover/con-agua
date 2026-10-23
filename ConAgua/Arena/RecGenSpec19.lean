import ConAgua.Arena.RecGenSpec18

/-!
# `classMajors` (lane `indproofs3`, helper `indproofs3-pos-cls`)

Every class key checked as a major: the key's application (`intern_const`, the `mk_app_n` stub),
`target_major_of`, `target_major_pins`; a recursion consing each major onto the rest's slice (D18).
-/

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## Frames -/

theorem tptW_mfr : ∀ (n : Nat) (m m' : Mem) (vis d xo xl : Word) (r : List Word),
    tptW stubCall n m vis d xo xl = some (r, m') → MFr [] [] m m'
  | 0, _, _, _, _, _, _, _, h => by simp [tptW] at h
  | n + 1, m, m', vis, d, xo, xl, r, h => by
    by_cases hl : xl = 0
    · rw [tptW_nil stubCall n m vis d xo xl hl] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
    rw [tptW_cons stubCall n m vis d xo xl hl] at h
    cases h1 : stubCall n "infer_type_core" [vis, d, rdW (m.arr64 IW) xo] m with
    | none => rw [h1] at h; simp [tptK] at h
    | some x =>
    obtain ⟨r1, m1⟩ := x
    rw [h1, tptK_some] at h
    refine (MFr.ofStub h1).trans ?_
    cases h2 : tptW stubCall n m1 vis d (xo + 1) (xl - 1) with
    | none => rw [h2] at h; simp [tptK2] at h
    | some y =>
    obtain ⟨r2, m2⟩ := y
    rw [h2, tptK2_some] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact tptW_mfr n _ _ _ _ _ _ _ h2

theorem tmpW_mfr {N : Nat} {m m' : Mem} {vis rP M : Word} {r : List Word} (h : tmpW stubCall N m vis rP M = some (r, m')) :
    MFr [] [] m m' := by
  cases N with
  | zero => simp [tmpW] at h
  | succ N =>
  by_cases hm : rdW (m.arr64 IW) (M + 8) ≠ 0
  · rw [tmpW_mem stubCall N m vis rP M hm] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; rw [← h.2]; exact MFr.refl _ _ _
  rw [tmpW_out stubCall N m vis rP M hm] at h
  cases h1 : tptW stubCall N m vis rP (rdW (m.arr64 IW) (M + 2)) (rdW (m.arr64 IW) (M + 3)) with
  | none => rw [h1] at h; simp [tmpK1] at h
  | some x =>
  obtain ⟨r1, m1⟩ := x
  rw [h1, tmpK1_some] at h
  refine (tptW_mfr _ _ _ _ _ _ _ _ h1).trans ?_
  cases h2 : ceinternW m1 (rdW (m1.arr64 IW) M) (rdW (m1.arr64 IW) (M + 1)) with
  | none => rw [h2] at h; simp [tmpK2] at h
  | some y =>
  obtain ⟨hd, m2⟩ := y
  rw [h2, tmpK2_some] at h
  refine (ceinternW_mfr h2).trans ?_
  by_cases hb : 4294967296 ≤ hd
  · rw [if_pos hb] at h; cases h
  rw [if_neg hb] at h
  cases h3 : mknF m2 [hd, rdW (m2.arr64 IW) (M + 2), rdW (m2.arr64 IW) (M + 3)] with
  | none => rw [h3] at h; simp [tmpK3] at h
  | some z =>
  obtain ⟨r3, m3⟩ := z
  rw [h3, tmpK3_some] at h
  refine (MFr.ofMknF h3).trans ?_
  cases h4 : stubCall N "infer_type_core" [vis, rP, r3.headD 0] m3 with
  | none => rw [h4] at h; simp [tmpK4] at h
  | some w =>
  obtain ⟨r4, m4⟩ := w
  rw [h4, tmpK4_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  rw [← h.2]; exact MFr.ofStub h4

/-! ## `class_majors` -/

mutual
/-- **The model of `class_majors(vis, pp, cao, cal, pfo, pfl, ko, kl)`** at exec fuel `n`. -/
def clmW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word →
    Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, vis, pp, cao, cal, pfo, pfl, ko, kl =>
    if kl = 0 then some ([0, 0], m)
    else clmK1 p n vis pp cao cal pfo pfl ko kl (rdW (m.arr64 IW) ko)
      (callW p n "intern_const" [rdW (m.arr64 IW) (rdW (m.arr64 IW) ko),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) ko + 1)] m)
def clmK1 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl key : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => if 4294967296 ≤ r.headD 0 then none
      else clmK2 p n vis pp cao cal pfo pfl ko kl (callW p n "mk_app_n_f"
        [r.headD 0, rdW (m.arr64 IW) (key + 2), rdW (m.arr64 IW) (key + 3)] m)
def clmK2 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => clmK3 p n vis pp cao cal pfo pfl ko kl
      (callW p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, pfo, pfl, r.headD 0] m)
def clmK3 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => clmK4 p n vis pp cao cal pfo pfl ko kl r
      (callW p n "target_major_pins" [vis, rdW (m.arr64 IW) (pp + 4), r.headD 0] m)
def clmK4 (p : Prog) (n : Nat) (vis pp cao cal pfo pfl ko kl : Word) (r3 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m) => ckkK2 p n r3 (clmW p n m vis pp cao cal pfo pfl (ko + 1) (kl - 1))
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp cao cal pfo pfl ko kl key : Word) (r r3 : List Word)
theorem clmW_zero : clmW p 0 m vis pp cao cal pfo pfl ko kl = none := by simp [clmW]
theorem clmW_nil (h : kl = 0) : clmW p (n + 1) m vis pp cao cal pfo pfl ko kl = some ([0, 0], m) := by
  simp [clmW, h]
theorem clmW_cons (h : kl ≠ 0) : clmW p (n + 1) m vis pp cao cal pfo pfl ko kl =
    clmK1 p n vis pp cao cal pfo pfl ko kl (rdW (m.arr64 IW) ko)
      (callW p n "intern_const" [rdW (m.arr64 IW) (rdW (m.arr64 IW) ko),
        rdW (m.arr64 IW) (rdW (m.arr64 IW) ko + 1)] m) := by simp [clmW, h]
theorem clmK1_some : clmK1 p n vis pp cao cal pfo pfl ko kl key (some (r, m)) =
    if 4294967296 ≤ r.headD 0 then none
      else clmK2 p n vis pp cao cal pfo pfl ko kl (callW p n "mk_app_n_f"
        [r.headD 0, rdW (m.arr64 IW) (key + 2), rdW (m.arr64 IW) (key + 3)] m) := by simp [clmK1]
theorem clmK2_some : clmK2 p n vis pp cao cal pfo pfl ko kl (some (r, m)) = clmK3 p n vis pp cao cal pfo pfl ko kl
      (callW p n "target_major_of" [vis, pp, cao, cal, pfo, pfl, pfo, pfl, r.headD 0] m) := by simp [clmK2]
theorem clmK3_some : clmK3 p n vis pp cao cal pfo pfl ko kl (some (r, m)) = clmK4 p n vis pp cao cal pfo pfl ko kl r
      (callW p n "target_major_pins" [vis, rdW (m.arr64 IW) (pp + 4), r.headD 0] m) := by simp [clmK3]
theorem clmK4_some : clmK4 p n vis pp cao cal pfo pfl ko kl r3 (some (r, m)) =
    ckkK2 p n r3 (clmW p n m vis pp cao cal pfo pfl (ko + 1) (kl - 1)) := by simp [clmK4]
end arms
attribute [ind_grind] clmW_nil clmW_cons clmK1_some clmK2_some clmK3_some clmK4_some

set_option maxHeartbeats 1600000 in
theorem clm_spec (p : Prog) (hp : p.lookup "class_majors" = some classMajorsL) (n : Nat) :
    ∀ (s₀ : St) (vis pp cao cal pfo pfl ko kl : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "class_majors" [vis, pp, cao, cal, pfo, pfl, ko, kl]
    ⦃fun r s' => LocEq s' s₀ ∧ clmW p n s₀.mem vis pp cao cal pfo pfl ko kl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis pp cao cal pfo pfl ko kl; rw [invoke_eq _ hp]; simp only [callFn, classMajorsL]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis pp cao cal pfo pfl ko kl
    rw [invoke_eq _ hp]
    simp only [callFn, classMajorsL]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        callW_spec p n "intern_const", callW_spec p n "mk_app_n_f", callW_spec p n "target_major_of",
        callW_spec p n "target_major_pins", callW_spec p n "sl_cons", ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq]

/-- The lookups of `class_majors`. -/
structure ClmProg (p : Prog) : Prop where
  tmf : TmfProg p
  tmp : TmpProg p
  keys : KeysProg p
  cm : p.lookup "class_majors" = some classMajorsL

/-- **`class_majors`' model simulates `classMajors`.** -/
theorem clmW_sim {p : Prog} (hP : ClmProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (hcs : CtorSums fe) (pp cao cal pfo pfl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (n : Nat) (hn : 2 ^ 31 + n ≤ coreWalkFuel) :
    ∀ (m : Mem) (a : AState) (ko kl : Word) (ks : List ClassKey),
    StageR dn vis fe m a → DecB (fun m => decBS m pp.toNat) m bs → ShapeSrc m pp →
    PSlR decCNS css cao cal m → DecB (fun m => decHL m pfo.toNat pfl.toNat) m pfvs →
    pfo.toNat + pfl.toNat ≤ iwTop m → PSlR decCK ks ko kl m → PosMR m →
    Sim (clmW p n m vis pp cao cal pfo pfl ko kl) (ConRon.Arena.classMajors V fe bs css pfvs ks) a
      (fun r x m' a' => StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PSlR decTM x (r.headD 0) (r.tail.headD 0) m' ∧
        PosMR m') := by
  induction n with
  | zero => intro m a ko kl ks _ _ _ _ _ _ _ _; rw [clmW_zero]; exact Sim.of_none
  | succ n ih =>
  intro m a ko kl ks hS hq hsrc hcss hpf hpfb hks hPm
  have hT : iwTop m < 2 ^ 64 := Nat.lt_of_le_of_lt hS.2.1 hS.2.2.2.1
  by_cases hkl : kl = 0
  · rw [clmW_nil p n m vis pp cao cal pfo pfl ko kl hkl]
    have : ks = [] := by
      have h := hks.1; simp only [DecB, hkl] at h
      simpa [decPL] using h.symm
    subst this
    exact Sim.ret ⟨hS, IWGrow.refl m, PSlR.nil decTM m, hPm⟩
  obtain ⟨q, k0, ks', rfl, hw, hqb, hdk, hks'⟩ := partsPSl_cons hks hkl
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  rw [clmW_cons p n m vis pp cao cal pfo pfl ko kl hkl, hw]
  rw [← hq'] at hdk
  obtain ⟨nk, hnk, rfl⟩ := decCK_decB_nk hdk
  obtain ⟨hcH, hcd, huH, hud, hds, hdsb, hk4⟩ := pos2_nk_fields hnk hT
  simp only [ConRon.Arena.classMajors, ckOfNk]
  -- the head
  refine Sim.bindK (K := clmK1 p n vis pp cao cal pfo pfl ko kl (UInt64.ofNat q)) (by simp [clmK1])
    (fun r m₁ => clmK1_some p n m₁ vis pp cao cal pfo pfl ko kl _ r)
    (Q := fun r x m' a' => decE (r.headD 0) = x ∧ StageR dn vis fe m' a' ∧ IWGrow m m' ∧ PosMR m') ?_ ?_
  · intro r1 m1 e1
    obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
      (internConst_spec p hP.tmp.cf hP.tmp.cp hP.tmp.ic n _ _ _) e1
    obtain ⟨a', hrun, hS1, hg1⟩ := internConst_stage hS _ _ hcH huH hW1
    rw [hcd, hud] at hrun
    exact ⟨_, a', hrun, rfl, hS1, hg1, hPm.fr (ceinternW_mfr hW1)⟩
  rintro r1 hd m1 a1 ⟨rfl, hS1, hg1, hP1⟩
  by_cases hb : 4294967296 ≤ r1.headD 0
  · rw [if_pos hb]; exact Sim.of_none
  rw [if_neg hb]
  have hr1H : H (r1.headD 0) := lt_of_notbig hb
  have hkq : (UInt64.ofNat q : Word).toNat + 4 ≤ iwTop m := hk4
  have e2 : rdW (m1.arr64 IW) (UInt64.ofNat q + 2) = rdW (m.arr64 IW) (UInt64.ofNat q + 2) := by
    have e : (UInt64.ofNat q + 2 : Word).toNat = (UInt64.ofNat q : Word).toNat + 2 :=
      word_add_toNat (by rw [show (2 : Word).toNat = 2 from rfl]; omega)
    simp only [rdW, e]; rw [hg1.2.2.1 _ (by omega)]
  have e3 : rdW (m1.arr64 IW) (UInt64.ofNat q + 3) = rdW (m.arr64 IW) (UInt64.ofNat q + 3) := by
    have e : (UInt64.ofNat q + 3 : Word).toNat = (UInt64.ofNat q : Word).toNat + 3 :=
      word_add_toNat (by rw [show (3 : Word).toNat = 3 from rfl]; omega)
    simp only [rdW, e]; rw [hg1.2.2.1 _ (by omega)]
  rw [e2, e3]
  have hds1 : decHL m1 (rdW (m.arr64 IW) (UInt64.ofNat q + 2)).toNat (rdW (m.arr64 IW) (UInt64.ofNat q + 3)).toNat =
      some nk.ds := by rw [decHL_agree (RdS.of_grow hg1) hdsb]; exact hds
  -- the application
  refine Sim.bindK (K := clmK2 p n vis pp cao cal pfo pfl ko kl) (by simp [clmK2])
    (fun r m₁ => clmK2_some p n m₁ vis pp cao cal pfo pfl ko kl r)
    (Q := fun r x m' a' => decW0E m' r x ∧ StageR dn vis fe m' a' ∧ IWGrow m1 m' ∧ PosMR m') ?_ ?_
  · intro r2 m2 e2
    obtain ⟨s2, rfl, -, hs2⟩ := triple_of_callW (s₀ := ⟨m1, Locals.init []⟩)
      (mknF_spec p hP.tmp.ad n _ [r1.headD 0, _, _]) e2
    obtain ⟨x, a', hrun, hS2, hg2, hx⟩ := mknF_ok dn vis fe _ _ _ hr1H nk.ds m1 s2.mem a1 r2 hs2 ⟨hS1, hds1⟩
    exact ⟨x, a', hrun, hx, hS2, hg2, hP1.fr (MFr.ofMknF hs2)⟩
  rintro r2 mty m2 a2 ⟨⟨hmH, hmd⟩, hS2, hg2, hP2⟩
  have hg02 := hg1.trans hg2
  -- the major
  refine Sim.bindK (K := clmK3 p n vis pp cao cal pfo pfl ko kl) (by simp [clmK3])
    (fun r m₁ => clmK3_some p n m₁ vis pp cao cal pfo pfl ko kl r)
    (Q := fun r x m' a' => DecB (fun m => decTM m (r.headD 0).toNat) m' x ∧ StageR dn vis fe m' a' ∧
      IWGrow m2 m' ∧ PosMR m') ?_ ?_
  · cases n with
    | zero => intro r m' e; rw [callW_zero] at e; cases e
    | succ k =>
    rw [← hmd]
    exact installSimCall (targetMajorOf_refines hP.tmf dn vis fe hcs k (by omega) _ a2 pp cao cal pfo pfl pfo pfl
        (r2.headD 0) bs css pfvs pfvs hS2 (hq.grow (decBS_mono _) hg02)
        (partsHsrc_grow hg02 (partsShapeFacts hq hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg02)
        (hpf.grow (OMono.decHL _ _) hg02) (hpf.grow (OMono.decHL _ _) hg02) (Nat.le_trans hpfb hg02.1) hmH hP2)
      fun r s' ⟨_, hok, h1, h2, h3, h4⟩ => ⟨hok, h1, h2, h3, h4⟩
  rintro r3 tm m3 a3 ⟨hd3, hS3, hg3, hP3⟩
  have hg03 := hg02.trans hg3
  obtain ⟨hnpw, hnpb, -, -⟩ := partsShapeWords hg03 hq (partsShapeFacts hq hsrc).2.1
  -- the pins
  refine Sim.bindK (K := clmK4 p n vis pp cao cal pfo pfl ko kl r3) (by simp [clmK4])
    (fun r m₁ => clmK4_some p n m₁ vis pp cao cal pfo pfl ko kl r r3)
    (Q := fun _ _ m' a' => StageR dn vis fe m' a' ∧ IWGrow m3 m' ∧ PosMR m') ?_ ?_
  · intro r4 m4 e4
    obtain ⟨s4, rfl, -, hW4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (targetMajorPins_spec p hP.tmp stubCall (stubCall_spec p) n _ vis _ _) e4
    obtain ⟨s4', hs4', -, hok, hS4, hg4⟩ := triple_of_callW (s₀ := ⟨m3, Locals.init []⟩)
      (targetMajorPins_refines p hP.tmp n _ a3 dn vis fe _ _ tm hS3 hd3) e4
    rw [hnpw, UInt64.toNat_ofNat_of_lt' hnpb] at hok hS4
    rw [hs4'] at hS4 hg4
    exact ⟨_, _, partsRunOfOk hok, hS4, hg4, hP3.fr (tmpW_mfr hW4)⟩
  rintro r4 - m4 a4 ⟨hS4, hg4, hP4⟩
  have hg04 := hg03.trans hg4
  -- the rest
  refine Sim.bindK (K := ckkK2 p n r3) (body := fun r5 m5 => ckkK3 (callW p n "sl_cons"
      [r3.headD 0, r5.headD 0, r5.tail.headD 0] m5)) rfl (fun _ _ => rfl)
    (ih (by omega) m4 a4 (ko + 1) (kl - 1) ks' hS4 (hq.grow (decBS_mono _) hg04)
      (partsHsrc_grow hg04 (partsShapeFacts hq hsrc).2.1 hsrc) (hcss.grow decCNS_mono hg04)
      (hpf.grow (OMono.decHL _ _) hg04) (Nat.le_trans hpfb hg04.1) (hks'.grow decCK_mono hg04) hP4) ?_
  rintro r5 xs m5 a5 ⟨hS5, hg5, hd5, hP5⟩
  refine Sim.mstep (K := ckkK3) rfl (fun _ _ => rfl) fun r6 m6 h6 => ?_
  obtain ⟨hS6, hg6, hd6, hf6⟩ := clsCons hP.keys decTM_mono h6 hS5 hd5 (hd3.grow (decTM_mono _) (hg4.trans hg5))
  exact Sim.ret ⟨hS6, (hg04.trans hg5).trans hg6, by simpa using hd6, hP5.fr hf6⟩

/-- **`class_majors` refines `classMajors`** (through `target_major_of`'s and `target_major_pins`'
stubs): the keys a slice of `ClassKey` records decoded below the tops; the classes a slice of fresh
`TargetMajor` records. Under `StageR`; the census link is `classMajors_refinesC`. -/
theorem classMajors_refines {p : Prog} (hP : ClmProg p) (dn : NIdx → Option ConLeche.Name) (vis : Word)
    (fe : IFEnv) (hcs : CtorSums fe) (n : Nat) (hn : 2 ^ 31 + n ≤ coreWalkFuel) (s₀ : St) (a₀ : AState)
    (pp cao cal pfo pfl ko kl : Word) (bs : BlockShape) (css : List (List (IConstantVal × Nat)))
    (pfvs : List EIdx) (ks : List ClassKey) (hS : StageR dn vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hsrc : ShapeSrc s₀.mem pp)
    (hcss : PSlR decCNS css cao cal s₀.mem) (hpf : DecB (fun m => decHL m pfo.toNat pfl.toNat) s₀.mem pfvs)
    (hpfb : pfo.toNat + pfl.toNat ≤ iwTop s₀.mem) (hks : PSlR decCK ks ko kl s₀.mem) (hPm : PosMR s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_majors" [vis, pp, cao, cal, pfo, pfl, ko, kl]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.classMajors V fe bs css pfvs ks) a₀ ∧
      StageR dn vis fe s'.mem (AM.st (ConRon.Arena.classMajors V fe bs css pfvs ks) a₀) ∧ IWGrow s₀.mem s'.mem ∧
      PSlR decTM (AM.res (ConRon.Arena.classMajors V fe bs css pfvs ks) a₀) (r.headD 0) (r.tail.headD 0) s'.mem ∧
      PosMR s'.mem; ⊤⦄ :=
  triple_post (clm_spec p hP.cm n s₀ vis pp cao cal pfo pfl ko kl) fun _ _ ⟨hl, hm⟩ =>
    let ⟨hok, hQ⟩ := Sim.run (clmW_sim hP dn vis fe hcs pp cao cal pfo pfl bs css pfvs n hn _ a₀ ko kl ks hS hq hsrc
      hcss hpf hpfb hks hPm) hm
    ⟨hl, hok, hQ⟩

end L.Ind
