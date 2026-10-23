import ConAgua.Arena.RecGenSpec9
import ConAgua.Arena.IndRealNames

/-!
# `RecGen`: `classRecsRulesOk` (lane `indproofs2`, helper `rec3`)

The result list `(cvG, M, rhss)` is a pointer slice of `rec4` records decoded below the tops
(`decRR`); `target_major_at`'s record is decoded below the tops too (`rec3TMA_sim`: a stored class,
or the fresh default record, whose slices are empty).
-/


noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `target_major_at`'s record, decoded below the tops -/

/-- A `TargetMajor` record below the top with empty slices reads the same in the cut pools. -/
theorem rec3DecTM_trunc {m : Mem} {q : Nat} (hq : q + 13 ≤ iwTop m) (h3 : iwN m (q + 3) = some 0)
    (h7 : iwN m (q + 7) = some 0) (h10 : iwN m (q + 10) = some 0) (h12 : iwN m (q + 12) = some 0) :
    decTM (truncM m) q = decTM m q := by
  have e : ∀ k, k < 13 → iwN (truncM m) (q + k) = iwN m (q + k) := fun k hk => iwN_truncM (by omega)
  have eh : ∀ {kk : IdxKind} k, k < 13 → (iwH (truncM m) (q + k) : Option (Idx kk)) = iwH m (q + k) :=
    fun k hk => iwH_truncM (by omega)
  have eh0 : ∀ {kk : IdxKind}, (iwH (truncM m) q : Option (Idx kk)) = iwH m q := eh 0 (by omega)
  simp only [decTM, decAt, Nat.add_assoc, Nat.reduceAdd, eh0, eh 1 (by omega), e 2 (by omega),
    e 3 (by omega), e 4 (by omega), e 5 (by omega), e 6 (by omega), e 7 (by omega), e 8 (by omega),
    e 9 (by omega), e 10 (by omega), e 11 (by omega), e 12 (by omega), h3, h7, h10, h12]
  simp [decHL, hslice?, decPL]

/-- **`target_major_default`'s record is decoded below the tops.** -/
theorem rec3TmdW_decB {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {a : AState}
    {m m' : Mem} {r : List Word} {tm : TargetMajor} (h : tmdW m = some (r, m')) (hS : StageR dn vis fe m a)
    (hd : decTM m' (r.headD 0).toNat = some tm) : DecB (fun m => decTM m (r.headD 0).toNat) m' tm := by
  rw [tmdW_eq] at h
  cases h1 : naF m [] with
  | none => rw [h1] at h; simp [tmdK1] at h
  | some x1 =>
  obtain ⟨ra, m1⟩ := x1
  rw [h1, tmdK1_some] at h
  obtain ⟨_x1, _a1, _hr1, hS1, _hg1, _hw1, _hl1⟩ := naF_ok dn vis fe m m1 a ra h1 hS
  cases hp : pinWordV m1 52 with
  | none => rw [hp] at h; simp [tmdK2] at h
  | some ls =>
  rw [hp, tmdK2_some] at h
  cases hmk : mkTMW m1 (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 with
  | none => rw [hmk] at h; simp [tmdK3] at h
  | some x3 =>
  obtain ⟨r3, m2⟩ := x3
  rw [hmk, tmdK3_some] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨-, -, hsz, -, hc⟩ := hS1.2
  simp only [mkTMW] at hmk
  cases hal : allocW m1 13 with
  | none => rw [hal] at hmk; simp at hmk
  | some qm =>
  obtain ⟨q, m1a⟩ := qm
  rw [hal] at hmk
  simp only [Option.some.injEq, Prod.mk.injEq] at hmk
  obtain ⟨rfl, rfl⟩ := hmk
  obtain ⟨hq, rfl, hroom⟩ := allocW_facts hal hsz
  subst hq
  have hroom' : (rdW (m1.arr64 CTL) 200).toNat + 13 ≤ (m1.arr64 IW).size := by simpa using hroom
  have hmem : tmWr (allocMem m1 13) (rdW (m1.arr64 CTL) 200) (ra.headD 0) ls 0 0 0 0 0 0 0 0 0 0 0 =
      wrIW (allocMem m1 13) (rdW (m1.arr64 CTL) 200)
        [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
    rw [← tmMem_eq]; rfl
  obtain ⟨hget, -, -, htop⟩ := recMem_post m1 [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 13 rfl hc
    (by simpa using hroom') hsz
  simp only [List.headD_cons] at hd ⊢
  rw [hmem] at hd ⊢
  have hz : ∀ k (hk : k < 13),
      iwN (wrIW (allocMem m1 13) (rdW (m1.arr64 CTL) 200) [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0])
        ((rdW (m1.arr64 CTL) 200).toNat + k) =
        some (([ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] : List Word)[k]'(by simpa using hk)).toNat := by
    intro k hk
    simp only [iwN, nat?, iwA, hget k (by simpa using hk)]
    rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have htop' : iwTop (wrIW (allocMem m1 13) (rdW (m1.arr64 CTL) 200)
      [ra.headD 0, ls, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) = (rdW (m1.arr64 CTL) 200).toNat + 13 := by
    simp only [iwTop, htop]; rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; omega
  show decTM (truncM _) _ = some tm
  rw [rec3DecTM_trunc (by omega) (hz 3 (by omega)) (hz 7 (by omega)) (hz 10 (by omega)) (hz 12 (by omega))]
  exact hd

/-- **`target_major_at`, its record decoded below the tops.** -/
theorem rec3TMA_sim (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv) (n : Nat) (m : Mem)
    (a : AState) (mo ml c : Word) (ms : List TargetMajor) (hS : StageR dn vis fe m a)
    (hms : DecB (fun m => decPL m (decTM m) mo.toNat ml.toNat) m ms) (hb : mo.toNat + ml.toNat < 2 ^ 64) :
    RSim (tmaW n m mo ml c) (ConRon.Arena.targetMajorAt ms c.toNat) a
      (fun b a' tm => StageR dn vis fe b.2 a' ∧ IWGrow m b.2 ∧
        DecB (fun m => decTM m (b.1.headD 0).toNat) b.2 tm) := by
  have hms0 : decPL m (decTM m) mo.toNat ml.toNat = some ms :=
    hms.get (OMono.decPL (fun q => decTM_mono q) _ _)
  have hlen := decPL_length m hms0
  intro b hb'
  obtain ⟨tm, a', hrun, hS', hg, hd⟩ := tmaW_sim dn vis fe n m a mo ml c ms hS hms0 hb b hb'
  refine ⟨tm, a', hrun, hS', hg, ?_⟩
  cases n with
  | zero => simp [tmaW] at hb'
  | succ n =>
  by_cases hcl : c < ml
  · rw [tmaW_hit n m mo ml c hcl] at hb'
    cases hb'
    have hc' : c.toNat < ml.toNat := UInt64.lt_iff_toNat_lt.mp hcl
    obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hms c.toNat hc'
    obtain ⟨-, hv'⟩ := rec2IwN_trunc hv
    have hrd := iwN_rdW_at (w := mo) (k := c.toNat) hv' hS.2.2.2.1
    have hcw : mo + UInt64.ofNat c.toNat = mo + c := by simp
    rw [hcw] at hrd
    have hrun' : ConRon.Arena.targetMajorAt ms c.toNat = pure (ms[c.toNat]'(by omega)) := by
      simp [ConRon.Arena.targetMajorAt, List.getElem?_eq_getElem (by omega : c.toNat < ms.length)]
    rw [hrun'] at hrun
    have hx : ms[c.toNat]'(by omega) = tm := by injection hrun with e; injection e
    simp only [List.headD_cons]
    rw [hrd.1, UInt64.toNat_ofNat_of_lt' hrd.2, ← hx]
    exact (show DecB (fun m => decTM m v) m _ from hdv).grow (decTM_mono _) (IWGrow.refl m)
  · rw [tmaW_miss n m mo ml c hcl] at hb'
    cases ho : fuelW n (tmdW m) with
    | none => rw [ho] at hb'; cases hb'
    | some b0 =>
    obtain ⟨r0, m0⟩ := b0
    rw [ho, tmaK_some] at hb'
    cases hb'
    cases n with
    | zero => cases ho
    | succ n =>
    simp only [fuelW_succ] at ho
    simp only [List.headD_cons] at hd ⊢
    exact rec3TmdW_decB ho hS hd

/-! ## The `rec4` records -/

/-- `IConstantVal × TargetMajor × List EIdx` at `p`: `[cv, M, rhss.off, rhss.len]`. -/
def decRR (m : Mem) (p : Nat) : Option (IConstantVal × TargetMajor × List EIdx) := do
  let cvp ← iwN m p
  let cv ← decCVp m cvp
  let mp ← iwN m (p + 1)
  let M ← decTM m mp
  let rhss ← decAt m (decHL m) (p + 2)
  pure (cv, M, rhss)

theorem decRR_mono (p : Nat) : OMono (fun m => decRR m p) := by
  unfold decRR
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decHL
    | apply OMono.decCVp
    | apply OMono.decAt
    | apply decTM_mono
    | apply OMono.bind
    | intro _)

/-- The slice of results: decoded below the tops, and below the top. -/
def decRRS (m' : Mem) (r : List Word) (xs : List (IConstantVal × TargetMajor × List EIdx)) : Prop :=
  DecB (fun m => decPL m (decRR m) (r.headD 0).toNat (r.tail.headD 0).toNat) m' xs ∧
    (r.headD 0).toNat + (r.tail.headD 0).toNat ≤ iwTop m'

/-- A fresh `rec4` record of decoded-below-the-tops parts is decoded below the tops. -/
theorem rec3Rec4_decB {m m' : Mem} {cvw mw ro rl : Word} {q : Nat} {cv : IConstantVal} {M : TargetMajor}
    {rhss : List EIdx} (hget : ∀ j < 4, (m'.arr64 IW)[q + j]? = [cvw, mw, ro, rl][j]?)
    (hq : q + 4 ≤ iwTop m') (hg : IWGrow m m')
    (hcv : DecB (fun m => decCVp m cvw.toNat) m cv) (hM : DecB (fun m => decTM m mw.toNat) m M)
    (hr : DecB (fun m => (decHL m ro.toNat rl.toNat : Option (List EIdx))) m rhss) :
    DecB (fun m => decRR m q) m' (cv, M, rhss) := by
  have hw : ∀ j (hj : j < 4), iwN (truncM m') (q + j) = some ([cvw, mw, ro, rl][j]'(by simpa using hj)).toNat :=
    fun j hj => by
      rw [iwN_truncM (by omega)]
      simp only [iwN, nat?, iwA, hget j hj]
      rw [List.getElem?_eq_getElem (by simp; omega)]; rfl
  have h0 := hw 0 (by omega)
  have h1 := hw 1 (by omega)
  have h2 := hw 2 (by omega)
  have h3 := hw 3 (by omega)
  simp only [Nat.add_zero, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  show decRR (truncM m') q = _
  have e1 : decCVp (truncM m') cvw.toNat = some cv := hcv.grow (OMono.decCVp _) hg
  have e2 : decTM (truncM m') mw.toNat = some M := hM.grow (decTM_mono _) hg
  have e3 : (decHL (truncM m') ro.toNat rl.toNat : Option (List EIdx)) = some rhss := hr.grow (OMono.decHL _ _) hg
  simp only [decRR, decAt, h0, h1, Nat.add_assoc, Nat.reduceAdd, h2, h3, Option.bind_eq_bind,
    Option.bind_some, e1, e2, e3]
  rfl

/-! ## Stable constant slices -/

theorem rec3CVX {m : Mem} {p : Nat} {cv : IConstantVal} (h : StabD (fun m => decCVX m p) m cv) :
    decCVp m p = some cv ∧ CVExt m p := by
  have := h.get
  simp only [decCVX] at this
  split at this
  · exact ⟨this, by assumption⟩
  · cases this

/-- A stable constant record is decoded below the tops. -/
theorem rec3CVX_decB {m : Mem} {p : Nat} {cv : IConstantVal} (h : StabD (fun m => decCVX m p) m cv) :
    DecB (fun m => decCVp m p) m cv := by
  obtain ⟨h1, h2⟩ := rec3CVX h
  show decCV (erA (truncM m)) p = some cv
  rw [rec2DecCV_agree (a := erA m) (T := erTop m) (fun i hi => truncM_er_eq hi) h2.1 h2.2]
  exact h1

/-- A stable constant slice is decoded below the tops. -/
theorem rec3SPL_decB {m : Mem} {o l : Nat} {cvs : List IConstantVal} (h : SPL decCVX m o l cvs) :
    DecB (fun m => decPL m (decCVp m) o l) m cvs := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  show decPL (truncM m) (decCVp (truncM m)) o l = some cvs
  have e : decNL (truncM m) o l = some ps := decNL_decB hps hb
  rw [decPL_eq_bind, e]
  simp only [Option.bind_some]
  clear e hps hb
  induction hf with
  | nil => rfl
  | @cons q x qs xs h1 _ ih =>
    have e1 : decCVp (truncM m) q = some x := rec3CVX_decB h1
    simp only [List.mapM_cons, e1, ih]; rfl

theorem rec3SPL_uncons {m : Mem} {o l : Nat} {cvs : List IConstantVal} (h : SPL decCVX m o (l + 1) cvs) :
    ∃ p cv cvs', cvs = cv :: cvs' ∧ iwN m o = some p ∧ o < iwTop m ∧
      StabD (fun m => decCVX m p) m cv ∧ SPL decCVX m (o + 1) l cvs' := by
  obtain ⟨hb, ps, hps, hf⟩ := h
  rw [decNL_succ] at hps
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hps
  obtain ⟨p, hp, ps', hps', rfl⟩ := hps
  cases hf with
  | cons h1 h2 => exact ⟨p, _, _, rfl, hp, by omega, h1, by omega, ps', hps', h2⟩

/-! ## The model -/

/-- The constructors of class `c` (`g.ctors.getD c []`) as a slice. -/
def crrXs (m : Mem) (g c : Word) : Word × Word :=
  if c < rdW (m.arr64 IW) (g + 10) then
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c)),
     rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) + 1))
  else (0, 0)

def crrK5 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => some ([r5.headD 0, r5.tail.headD 0], m5)

def crrK4 (n : Nat) (y : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => crrK5 (consW n m4 y (r4.headD 0) (r4.tail.headD 0))

mutual
/-- **The model of `class_recs_rules_ok_go`.** -/
noncomputable def crrW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Word → Word → Word →
    Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, rco, rcl, cgo, cgl, vo, vl, co, cl =>
    if vl = 0 then some ([0, 0], m)
    else if cl = 0 then some ([0, 0], m)
    else crrK1 n visT visR g rco rcl cgo cgl vo vl co cl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
      (crsW n m visT visR g rco rcl cgo cgl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
        (crrXs m g (rdW (m.arr64 IW) co)).1 (crrXs m g (rdW (m.arr64 IW) co)).2)
noncomputable def crrK1 (n : Nat) (visT visR g rco rcl cgo cgl vo vl co cl cvG c : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => crrK2 n visT visR g rco rcl cgo cgl vo vl co cl cvG (r1.headD 0) (r1.tail.headD 0)
      (tmaW n m1 (rdW (m1.arr64 IW) (g + 3)) (rdW (m1.arr64 IW) (g + 4)) c)
noncomputable def crrK2 (n : Nat) (visT visR g rco rcl cgo cgl vo vl co cl cvG ro rl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => crrK3 n visT visR g rco rcl cgo cgl vo vl co cl (recW m2 4 [cvG, r2.headD 0, ro, rl])
noncomputable def crrK3 (n : Nat) (visT visR g rco rcl cgo cgl vo vl co cl : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r3, m3) =>
    crrK4 n (r3.headD 0) (crrW n m3 visT visR g rco rcl cgo cgl (vo + 1) (vl - 1) (co + 1) (cl - 1))
end

/-- **The model of `class_recs_rules_ok`.** -/
noncomputable def crraW : Nat → Mem → Word → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _, _ => none
  | n + 1, m, visT, visR, g, rco, rcl, cgo, cgl =>
    crrK5 (crrW n m visT visR g rco rcl cgo cgl cgo cgl rco rcl)

section arms
variable (n : Nat) (m m1 m2 m3 m4 m5 : Mem) (visT visR g rco rcl cgo cgl vo vl co cl cvG c ro rl y : Word)
  (r1 r2 r3 r4 r5 : List Word)
theorem crrXs_hit (h : c < rdW (m.arr64 IW) (g + 10)) : crrXs m g c =
    (rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c)),
     rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (g + 9) + c) + 1)) := by
  rw [crrXs, if_pos h]
theorem crrXs_miss (h : ¬ c < rdW (m.arr64 IW) (g + 10)) : crrXs m g c = (0, 0) := by
  rw [crrXs, if_neg h]
theorem crrW_nil1 (h : vl = 0) : crrW (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl = some ([0, 0], m) := by
  simp [crrW, h]
theorem crrW_nil2 (h1 : ¬ vl = 0) (h : cl = 0) :
    crrW (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl = some ([0, 0], m) := by
  simp only [crrW]; rw [if_neg h1, if_pos h]
theorem crrW_cons (h1 : ¬ vl = 0) (h : ¬ cl = 0) : crrW (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl =
    crrK1 n visT visR g rco rcl cgo cgl vo vl co cl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
      (crsW n m visT visR g rco rcl cgo cgl (rdW (m.arr64 IW) vo) (rdW (m.arr64 IW) co)
        (crrXs m g (rdW (m.arr64 IW) co)).1 (crrXs m g (rdW (m.arr64 IW) co)).2) := by
  simp only [crrW]; rw [if_neg h1, if_neg h]
theorem crrK1_some : crrK1 n visT visR g rco rcl cgo cgl vo vl co cl cvG c (some (r1, m1)) =
    crrK2 n visT visR g rco rcl cgo cgl vo vl co cl cvG (r1.headD 0) (r1.tail.headD 0)
      (tmaW n m1 (rdW (m1.arr64 IW) (g + 3)) (rdW (m1.arr64 IW) (g + 4)) c) := by rw [crrK1]
theorem crrK2_some : crrK2 n visT visR g rco rcl cgo cgl vo vl co cl cvG ro rl (some (r2, m2)) =
    crrK3 n visT visR g rco rcl cgo cgl vo vl co cl (recW m2 4 [cvG, r2.headD 0, ro, rl]) := by rw [crrK2]
theorem crrK3_some : crrK3 n visT visR g rco rcl cgo cgl vo vl co cl (some (r3, m3)) =
    crrK4 n (r3.headD 0) (crrW n m3 visT visR g rco rcl cgo cgl (vo + 1) (vl - 1) (co + 1) (cl - 1)) := by
  rw [crrK3]
theorem crrK4_some : crrK4 n y (some (r4, m4)) = crrK5 (consW n m4 y (r4.headD 0) (r4.tail.headD 0)) := rfl
theorem crrK5_some : crrK5 (some (r5, m5)) = some ([r5.headD 0, r5.tail.headD 0], m5) := rfl
theorem crraW_eq : crraW (n + 1) m visT visR g rco rcl cgo cgl =
    crrK5 (crrW n m visT visR g rco rcl cgo cgl cgo cgl rco rcl) := rfl
end arms

grind_pattern [ind_grind] crrXs_hit => crrXs m g c
grind_pattern [ind_grind] crrXs_miss => crrXs m g c
grind_pattern [ind_grind] crrW_nil1 => crrW (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl
grind_pattern [ind_grind] crrW_nil2 => crrW (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl
grind_pattern [ind_grind] crrW_cons => crrW (n + 1) m visT visR g rco rcl cgo cgl vo vl co cl
grind_pattern [ind_grind] crrK1_some => crrK1 n visT visR g rco rcl cgo cgl vo vl co cl cvG c (some (r1, m1))
grind_pattern [ind_grind] crrK2_some => crrK2 n visT visR g rco rcl cgo cgl vo vl co cl cvG ro rl (some (r2, m2))
grind_pattern [ind_grind] crrK3_some => crrK3 n visT visR g rco rcl cgo cgl vo vl co cl (some (r3, m3))
grind_pattern [ind_grind] crrK4_some => crrK4 n y (some (r4, m4))
grind_pattern [ind_grind] crrK5_some => crrK5 (some (r5, m5))
grind_pattern [ind_grind] crraW_eq => crraW (n + 1) m visT visR g rco rcl cgo cgl

/-- The lookups `class_recs_rules_ok` needs. -/
structure CrrProg (p : Prog) : Prop where
  crs : CrsProg p
  pw : p.lookup "pin_word" = some pinWordL
  mtm : p.lookup "mk_target_major" = some mkTargetMajor
  tmd : p.lookup "target_major_default" = some targetMajorDefault
  tma : p.lookup "target_major_at" = some targetMajorAt
  na : NaF p
  rec4 : p.lookup "rec4" = some rec4
  go : p.lookup "class_recs_rules_ok_go" = some classRecsRulesOkGo
  top : p.lookup "class_recs_rules_ok" = some classRecsRulesOkL

set_option maxHeartbeats 1000000 in
theorem classRecsRulesOkGo_spec (p : Prog) (h : CrrProg p) (n : Nat) :
    ∀ (s₀ : St) (visT visR g rco rcl cgo cgl vo vl co cl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_recs_rules_ok_go" [visT, visR, g, rco, rcl, cgo, cgl, vo, vl, co, cl]
    ⦃fun r s' => LocEq s' s₀ ∧ crrW n s₀.mem visT visR g rco rcl cgo cgl vo vl co cl = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ visT visR g rco rcl cgo cgl vo vl co cl
    rw [invoke_eq _ h.go]; simp only [callFn, classRecsRulesOkGo]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ visT visR g rco rcl cgo cgl vo vl co cl
    rw [invoke_eq _ h.go]
    simp only [callFn, classRecsRulesOkGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        classRulesOk_spec p h.crs n,
        targetMajorAt_spec p h.crs.alloc h.pw h.mtm h.tmd h.tma h.na n,
        rec4_specW p h.crs.alloc n h.rec4, slCons_specW p h.crs.alloc h.crs.copy h.crs.cons n, ih] <;>
      finish (gen := 20) (instances := 5000) [rdW_eq, loc_init4, loc_init5, loc_init6, loc_init7, loc_init8,
        loc_init9, loc_init10]

theorem classRecsRulesOk_spec (p : Prog) (h : CrrProg p) (n : Nat) (s₀ : St) (visT visR g rco rcl cgo cgl : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_recs_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl]
    ⦃fun r s' => LocEq s' s₀ ∧ crraW n s₀.mem visT visR g rco rcl cgo cgl = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ h.top]
  simp only [callFn, classRecsRulesOkL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, classRecsRulesOkGo_spec p h n] <;>
      finish (gen := 20) [loc_init4, loc_init5, loc_init6]

/-! ## The relational lemma -/

/-- The constructors of class `c`, as `class_recs_rules_ok_go` reads them. -/
theorem rec3CtorsAt {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv} {m : Mem} {a : AState}
    {g c : Word} {G : ClassGen} (hS : StageR dn vis fe m a) (hG : DecB (fun m => decCG m g.toNat) m G) :
    DecB (fun m' => decPL m' (decCC m') (crrXs m g c).1.toNat (crrXs m g c).2.toNat) m (G.ctors.getD c.toNat []) := by
  have hsz := hS.2.2.2.1
  obtain ⟨-, o9, l9, h9, h10, hct⟩ := rec3CG_parts hG
  obtain ⟨e9, t9⟩ := rec2RdN (w := g) (k := 9) h9 hsz
  obtain ⟨e10, t10⟩ := rec2RdN (w := g) (k := 10) h10 hsz
  simp only [show UInt64.ofNat 9 = (9 : Word) from rfl, show UInt64.ofNat 10 = (10 : Word) from rfl] at e9 e10
  have hlen : G.ctors.length = l9 := decPL_length _ hct
  by_cases hc : c < rdW (m.arr64 IW) (g + 10)
  · rw [crrXs_hit (h := hc)]
    rw [e10] at hc
    have hc' : c.toNat < l9 := by have := UInt64.lt_iff_toNat_lt.mp hc; rw [t10] at this; exact this
    obtain ⟨v, hv, hdv⟩ := decPL_getH (truncM m) hct c.toNat hc'
    obtain ⟨-, hvm⟩ := rec2IwN_trunc hv
    obtain ⟨ev, tv⟩ := rec2RdN (w := UInt64.ofNat o9) (k := c.toNat) (by rw [t9]; exact hvm) hsz
    simp only [UInt64.ofNat_toNat] at ev
    simp only [decLH] at hdv
    obtain ⟨xo, xl, hxo, hxl, hxs⟩ := decAt_some hdv
    obtain ⟨exo, txo⟩ := rec2RdN (w := UInt64.ofNat v) (k := 0) (by rw [tv]; exact (rec2IwN_trunc hxo).2) hsz
    obtain ⟨exl, txl⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [tv]; exact (rec2IwN_trunc hxl).2) hsz
    simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero,
      show UInt64.ofNat 1 = (1 : Word) from rfl] at exo exl
    simp only [e9, ev, exo, exl, txo, txl]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : c.toNat < G.ctors.length),
      Option.getD_some]
    exact hxs
  · rw [crrXs_miss (h := hc)]
    rw [e10] at hc
    have hc' : ¬ c.toNat < l9 := fun x => hc (by rw [← t10] at x; exact UInt64.lt_iff_toNat_lt.mpr x)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : G.ctors.length ≤ c.toNat),
      Option.getD_none]
    show decPL (truncM m) _ _ _ = some []
    simp [decPL]

theorem crrW_sim (dn : NIdx → Option ConLeche.Name) (visT visR : Word) (feR : IFEnv) (g rco rcl cgo cgl : Word)
    (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (hns : G.nP + G.slots.length < 2 ^ 64) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) (n : Nat) :
    ∀ (m : Mem) (a : AState) (vo vl co cl : Word) (cvs : List IConstantVal) (cs : List Nat),
    StageR dn visR feR m a → DecB (fun m => decCG m g.toNat) m G →
    DecB (fun m => decNL m rco.toNat rcl.toNat) m recCls → SPL decCVX m cgo.toNat cgl.toNat cvGs →
    SPL decCVX m vo.toNat vl.toNat cvs → DecB (fun m => decNL m co.toNat cl.toNat) m cs →
    RSim (crrW n m visT visR g rco rcl cgo cgl vo vl co cl)
      (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvs cs) a (KP dn visR feR m decRRS) := by
  induction n with
  | zero => intros; intro b hb; simp [crrW] at hb
  | succ n ih =>
  intro m a vo vl co cl cvs cs hS hG hrc hcg hcvs hcs
  have hsz := hS.2.2.2.1
  have hnil : RSim (some ([0, 0], m)) (Pure.pure [] : AM (List (IConstantVal × TargetMajor × List EIdx))) a
      (KP dn visR feR m decRRS) :=
    RSim.pure_some ⟨hS, IWGrow.refl m, by show decPL (truncM m) _ _ _ = some []; simp [decPL], by simp⟩
  by_cases hvl : vl = 0
  · rw [crrW_nil1 (h := hvl)]
    have : cvs = [] := by
      have := hcvs.length; rw [hvl] at this; exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecsRulesOk
    exact hnil
  obtain ⟨jv, hjv⟩ : ∃ j, vl.toNat = j + 1 :=
    ⟨vl.toNat - 1, by have : vl.toNat ≠ 0 := fun e => hvl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  obtain ⟨p, cv, cvs', rfl, hp, hpt, hcv, hcvsT⟩ := rec3SPL_uncons (by rw [← hjv]; exact hcvs)
  by_cases hcl : cl = 0
  · rw [crrW_nil2 (h1 := hvl) (h := hcl)]
    have : cs = [] := by
      have := decNL_length _ (hcs.get (OMono.decNL _ _)); rw [hcl] at this
      exact List.eq_nil_of_length_eq_zero (by simpa using this)
    subst this
    unfold ConRon.Arena.classRecsRulesOk
    exact hnil
  rw [crrW_cons (h1 := hvl) (h := hcl)]
  obtain ⟨jc, hjc⟩ : ∃ j, cl.toNat = j + 1 :=
    ⟨cl.toNat - 1, by have : cl.toNat ≠ 0 := fun e => hcl (UInt64.toNat_inj.mp (by simpa using e)); omega⟩
  have hcs' : decNL (truncM m) co.toNat (jc + 1) = some cs := by rw [← hjc]; exact hcs
  rw [decNL_succ] at hcs'
  simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hcs'
  obtain ⟨c0, hc0, cs', hcsT, rfl⟩ := hcs'
  obtain ⟨-, hc0m⟩ := rec2IwN_trunc hc0
  obtain ⟨ep, tp⟩ := rec2RdN (w := vo) (k := 0) (by simpa using hp) hsz
  obtain ⟨ec, tc⟩ := rec2RdN (w := co) (k := 0) (by simpa using hc0m) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, UInt64.add_zero] at ep ec
  rw [ep, ec]
  obtain ⟨hcvp, hcvx⟩ := rec3CVX hcv
  unfold ConRon.Arena.classRecsRulesOk
  dsimp only
  -- `class_rules_ok`
  have hxs := rec3CtorsAt (c := UInt64.ofNat c0) hS hG
  rw [tc] at hxs
  refine RSim.bind (K := crrK1 n visT visR g rco rcl cgo cgl vo vl co cl (UInt64.ofNat p) (UInt64.ofNat c0))
    (by rw [crrK1])
    (by
      have := crsW_sim dn visT visR feR g rco rcl cgo cgl (UInt64.ofNat p) (UInt64.ofNat c0) G recCls cvGs cv
        hns hrcb hcgb n m a _ _ _ hS hG hrc (rec3SPL_decB hcg) (by rw [tp]; exact hcvp) (by rw [tp]; exact hcvx)
        hxs
      rw [tc] at this
      exact this) ?_
  rintro ⟨r1, m1⟩ rhss a1 - ⟨hS1, hg1, hr1⟩
  dsimp only at hS1 hg1 hr1
  rw [crrK1_some]
  -- `target_major_at`
  have hG1 := hG.grow (decCG_mono _) hg1
  have hsz1 := hS1.2.2.2.1
  obtain ⟨-, -, ⟨o3, l3, h3, h4, hcls⟩, -⟩ := rec2CG_parts hG1
  obtain ⟨e3, t3⟩ := rec2RdN (w := g) (k := 3) h3 hsz1
  obtain ⟨e4, t4⟩ := rec2RdN (w := g) (k := 4) h4 hsz1
  simp only [show UInt64.ofNat 3 = (3 : Word) from rfl, show UInt64.ofNat 4 = (4 : Word) from rfl] at e3 e4
  rw [e3, e4]
  have hb3 : o3 + l3 < 2 ^ 64 := by
    by_cases hl : l3 = 0
    · have := iwN_rdW h3 (by have := hS1.2.1; have := (rec2CG_parts hG1).2.1; omega); omega
    · have := rec2DecB_PL_top hcls hl; have := hS1.2.1; omega
  have hM := rec3TMA_sim dn visR feR n m1 a1 (UInt64.ofNat o3) (UInt64.ofNat l3) (UInt64.ofNat c0) G.cls hS1 (by rw [t3, t4]; exact hcls)
    (by rw [t3, t4]; exact hb3)
  rw [tc] at hM
  refine RSim.bind (K := crrK2 n visT visR g rco rcl cgo cgl vo vl co cl (UInt64.ofNat p) (r1.headD 0)
    (r1.tail.headD 0)) (by rw [crrK2]) hM ?_
  rintro ⟨r2, m2⟩ M a2 - ⟨hS2, hg2, hMd⟩
  dsimp only at hS2 hg2 hMd
  rw [crrK2_some]
  -- `rec4`: L only
  refine RSim.lstep (K := crrK3 n visT visR g rco rcl cgo cgl vo vl co cl) (by rw [crrK3])
    fun ⟨r3, m3⟩ h3' => ?_
  obtain ⟨hS3, hg3, hr3, hget3, htop3⟩ := recW_stage h3' hS2 rfl
  rw [crrK3_some]
  have hg13 := hg2.trans hg3
  have hrec : DecB (fun m => decRR m (r3.headD 0).toNat) m3 (cv, M, rhss) := by
    rw [hr3]
    refine rec3Rec4_decB (m := m2) (fun j hj => hget3 j (by simpa using hj)) (by simp at htop3; simp [iwTop] at htop3 ⊢; omega) hg3
      ((rec3CVX_decB hcv).grow (OMono.decCVp _) ((hg1.trans hg2)) |> fun h => by rw [tp]; exact h) hMd
      ((decRL_decB hr1).grow (OMono.decHL _ _) hg2 |> fun h => by
        simp only [getD_zero, Nat.zero_add, getD_one] at h; exact h)
  -- the rest
  have hg03 := hg1.trans hg13
  have hvo1 := rec2ToNat_succ (o := vo) (i := vo.toNat) (Nat.le_refl _) (by have := hS.2.1; omega)
  have hco1 := rec2ToNat_succ (o := co) (i := co.toNat) (Nat.le_refl _) (by have := hS.2.1; have := (rec2IwN_trunc hc0).1; omega)
  have hvl1 := rec2ToNat_pred hvl
  have hcl1 := rec2ToNat_pred hcl
  refine RSim.bind (K := crrK4 n (r3.headD 0)) rfl
    (ih m3 a2 (vo + 1) (vl - 1) (co + 1) (cl - 1) cvs' cs' hS3 (hG.grow (decCG_mono _) hg03)
      (hrc.grow (OMono.decNL _ _) hg03) (hcg.grow hg03)
      (by rw [hvo1, hvl1, hjv]; exact hcvsT.grow hg03)
      (by rw [hco1, hcl1, hjc]; exact (show DecB (fun m => decNL m (co.toNat + 1) jc) m cs' from
        hcsT).grow (OMono.decNL _ _) hg03)) ?_
  rintro ⟨r4, m4⟩ rest a4 - ⟨hS4, hg4, hrs, hrsb⟩
  dsimp only at hS4 hg4 hrs hrsb
  rw [crrK4_some]
  refine RSim.lstep (K := crrK5) rfl fun ⟨r5, m5⟩ h5 => ?_
  obtain ⟨hS5, hg5, hd5, ht5⟩ := partsConsPL decRR_mono h5 hS4 hrsb hrs (hrec.grow (decRR_mono _) hg4)
  rw [crrK5_some]
  exact RSim.pure_some ⟨hS5, hg03.trans (hg4.trans hg5), by simpa using hd5,
    by simp only [List.headD_cons, List.tail_cons]; omega⟩

/-- **`class_recs_rules_ok` refines `classRecsRulesOk`** (through `class_rules_ok`'s stubs): the
recursors with their majors and rules, a slice of `rec4` records decoded below the tops. -/
@[refines ConRon.Arena.classRecsRulesOk]
theorem classRecsRulesOk_refines (p : Prog) (hp : CrrProg p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (visT visR : Word) (feR : IFEnv) (g rco rcl cgo cgl : Word)
    (G : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (hS : StageR dn visR feR s₀.mem a₀) (hG : DecB (fun m => decCG m g.toNat) s₀.mem G)
    (hns : G.nP + G.slots.length < 2 ^ 64)
    (hrc : DecB (fun m => decNL m rco.toNat rcl.toNat) s₀.mem recCls) (hrcb : rco.toNat + rcl.toNat < 2 ^ 64)
    (hcg : SPL decCVX s₀.mem cgo.toNat cgl.toNat cvGs) (hcgb : cgo.toNat + cgl.toNat < 2 ^ 64) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "class_recs_rules_ok" [visT, visR, g, rco, rcl, cgo, cgl]
    ⦃fun r s' => LocEq s' s₀ ∧
      AM.ok (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a₀ ∧
      KP dn visR feR s₀.mem decRRS (r, s'.mem)
        (AM.st (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a₀)
        (AM.res (ConRon.Arena.classRecsRulesOk V visT.toNat feR G recCls cvGs cvGs recCls) a₀); ⊤⦄ := by
  refine triple_post (classRecsRulesOk_spec p hp n s₀ visT visR g rco rcl cgo cgl) fun _ _ ⟨hl, hw⟩ => ⟨hl, ?_⟩
  cases n with
  | zero => simp [crraW] at hw
  | succ n =>
  rw [crraW_eq] at hw
  refine RSim.am (RSim.bindPure (K := crrK5) rfl (crrW_sim dn visT visR feR g rco rcl cgo cgl G recCls cvGs hns hrcb
    hcgb n s₀.mem a₀ cgo cgl rco rcl cvGs recCls hS hG hrc hcg hcg hrc) ?_) hw
  rintro ⟨r1, m1⟩ x a1 - ⟨hS1, hg1, hd1, hb1⟩
  rw [crrK5_some]
  exact RSim.pure_some ⟨hS1, hg1, by simpa using hd1, by simpa using hb1⟩

end L.Ind
