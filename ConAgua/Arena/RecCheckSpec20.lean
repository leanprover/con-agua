import ConAgua.Arena.RecCheckSpec19

/-!
# `RecCheck`: `consBlockRecsTF`, the recursion (lane `indproofs3`, helper `rec`)

`block_shape_major_idx_at`/`block_shape_rule_prefix_at` as word models (`bmjW`, `brpW`; helper
`parts`' refinements state them by triples only), the recursion over the family's `rec4` records.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## The major index and rule prefix of recursor `r` -/

def bmjW (m : Mem) (q r : Word) : Word :=
  if rdW (m.arr64 IW) (q + 3) ≤ r then 0
  else rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 2) + r) + 2)

def brpW (m : Mem) (q r : Word) : Word :=
  if rdW (m.arr64 IW) (q + 3) ≤ r then 0
  else rdW (m.arr64 IW) (rdW (m.arr64 IW) (rdW (m.arr64 IW) (q + 2) + r) + 1)

theorem mj_spec (p : Prog) (hp : p.lookup "block_shape_major_idx_at" = some blockShapeMajorIdxAt) (n : Nat)
    (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_major_idx_at" [q, r]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ res.headD 0 = bmjW s₀.mem q r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeMajorIdxAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [bmjW, rdW_eq]

theorem rp_spec (p : Prog) (hp : p.lookup "block_shape_rule_prefix_at" = some blockShapeRulePrefixAt) (n : Nat)
    (s₀ : St) (q r : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_rule_prefix_at" [q, r]
    ⦃fun res s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ res.headD 0 = brpW s₀.mem q r; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, blockShapeRulePrefixAt]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64] <;>
      finish [brpW, rdW_eq]

/-- The models at a shape record decoded below the tops. -/
theorem bmjW_rpW_eq {m : Mem} {q r : Word} {bs : BlockShape} (hq : DecB (fun m => decBS m q.toNat) m bs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) :
    (bmjW m q r).toNat = bs.majorIdxAt r.toNat ∧ (brpW m q r).toNat = bs.rulePrefixAt r.toNat := by
  have h' : decBS (truncM m) q.toNat = some bs := hq
  obtain ⟨-, hrecs, -⟩ := decBS_some h'
  obtain ⟨o, l, ho, hl, hd⟩ := decAt_some hrecs
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨hlt3, hlm⟩ := rec2IwN_trunc hl
  obtain ⟨e2, t2⟩ := rec2RdN (w := q) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := q) (k := 3) (by simpa using hlm) hsz
  simp only [show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl] at e2 e3
  have hlen := decPL_length (truncM m) hd
  unfold bmjW brpW BlockShape.majorIdxAt BlockShape.rulePrefixAt
  rw [e3, e2]
  by_cases hle : UInt64.ofNat l ≤ r
  · rw [ite_eq_left hle, ite_eq_left hle]
    have : bs.recs[r.toNat]? = none := by
      rw [List.getElem?_eq_none_iff, hlen]; have := UInt64.le_iff_toNat_le.mp hle; rw [t3] at this; exact this
    rw [this]; exact ⟨rfl, rfl⟩
  rw [ite_eq_right hle, ite_eq_right hle]
  have hrl : r.toNat < l := by
    have := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp hle); rwa [t3] at this
  obtain ⟨v, rc, hv, hrc, hget⟩ := decPL_get l o bs.recs hd r.toNat hrl
  rw [hget]
  obtain ⟨hvt, hvm⟩ := rec2IwN_trunc hv
  have hor : (UInt64.ofNat o + r).toNat = o + r.toNat := by
    rw [UInt64.toNat_add, t2]; exact Nat.mod_eq_of_lt (by
      have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hvt; omega)
  have hrd := iwN_rdW hvm (by have := (rdW (m.arr64 CTL) 200).toNat_lt; simp only [iwTop] at hvt; omega)
  have e : UInt64.ofNat (o + r.toNat) = UInt64.ofNat o + r := by
    apply UInt64.toNat_inj.mp; rw [hor]; simp; have := (rdW (m.arr64 CTL) 200).toNat_lt
    simp only [iwTop] at hvt; omega
  rw [e] at hrd
  rw [hrd.1]
  obtain ⟨-, hrP, hmI, -, -⟩ := decRS_some hrc
  obtain ⟨-, hrPm⟩ := rec2IwN_trunc hrP
  obtain ⟨-, hmIm⟩ := rec2IwN_trunc hmI
  have hvv : (UInt64.ofNat v : Word).toNat = v := UInt64.toNat_ofNat_of_lt' hrd.2
  obtain ⟨e1', t1'⟩ := rec2RdN (w := UInt64.ofNat v) (k := 1) (by rw [hvv]; exact hrPm) hsz
  obtain ⟨e2', t2'⟩ := rec2RdN (w := UInt64.ofNat v) (k := 2) (by rw [hvv]; exact hmIm) hsz
  simp only [show UInt64.ofNat 1 = (1 : Word) from rfl, show UInt64.ofNat 2 = (2 : Word) from rfl] at e1' e2'
  exact ⟨by rw [e2', t2'], by rw [e1', t1']⟩

/-! ## `cons_block_recs_tf` -/

def cbrK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0], m)

def cbrK2 (k : Mem → Word → Option (List Word × Mem)) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rv, m) => k m (rv.headD 0)

def cbrK1 (p : Prog) (n : Nat) (vis cv mI rP : Word) (k : Mem → Word → Option (List Word × Mem)) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rr, m) => cbrK2 k (cbpW p n m vis cv mI rP (rr.headD 0) (rr.tail.headD 0))

/-- **The model of `cons_block_recs_tf`** (exec fuel). -/
def cbrW (p : Prog) : Nat → Mem → Word → Word → Word → Word → Word → Word → Option (List Word × Mem)
  | 0, _, _, _, _, _, _, _ => none
  | n + 1, m, vis2, pp, mm, lo, ll, vis =>
    if ll = 0 then some ([vis], m)
    else cbrK1 p n vis (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (bmjW m pp mm) (brpW m pp mm)
      (fun m' v => cbrK3 (cbrW p n m' vis2 pp (mm + 1) (lo + 1) (ll - 1) v))
      (tsrW n m vis2 (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (brpW m pp mm)
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 1)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 3)))

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis2 pp mm lo ll vis cv mI rP v : Word) (r rr rv : List Word)
  (k : Mem → Word → Option (List Word × Mem))
theorem cbrW_nil (h : ll = 0) : cbrW p (n + 1) m vis2 pp mm lo ll vis = some ([vis], m) := by simp [cbrW, h]
theorem cbrW_cons (h : ¬ ll = 0) : cbrW p (n + 1) m vis2 pp mm lo ll vis =
    cbrK1 p n vis (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (bmjW m pp mm) (brpW m pp mm)
      (fun m' v => cbrK3 (cbrW p n m' vis2 pp (mm + 1) (lo + 1) (ll - 1) v))
      (tsrW n m vis2 (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo)) (brpW m pp mm)
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 1)) (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) lo + 3))) := by simp [cbrW, h]
theorem cbrK1_some : cbrK1 p n vis cv mI rP k (some (rr, m)) =
    cbrK2 k (cbpW p n m vis cv mI rP (rr.headD 0) (rr.tail.headD 0)) := rfl
theorem cbrK2_some : cbrK2 k (some (rv, m)) = k m (rv.headD 0) := rfl
theorem cbrK3_some : cbrK3 (some (r, m)) = some ([r.headD 0], m) := rfl
end arms
attribute [ind_grind] cbrW_nil cbrW_cons cbrK1_some cbrK2_some cbrK3_some

theorem cbr_spec (p : Prog) (L : CbrLook p) (n : Nat) :
    ∀ (s₀ : St) (vis2 pp mm lo ll vis : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_recs_tf" [vis2, pp, mm, lo, ll, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ cbrW p n s₀.mem vis2 pp mm lo ll vis = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ vis2 pp mm lo ll vis
    rw [invoke_eq _ L.cbr]; simp only [callFn, consBlockRecsTF]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ vis2 pp mm lo ll vis
    rw [invoke_eq _ L.cbr]
    simp only [callFn, consBlockRecsTF]
    sym (gen := 80) (instances := 20000) only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, mj_spec p L.mi n, rp_spec p L.rpa n,
        tsr_spec p L.tsr n, cbp_spec p L n, ih] <;>
      finish (gen := 40) (instances := 20000) [rdW_eq, loc_init4, loc_init5]

section rel
variable (dn : NIdx → Option ConLeche.Name)

theorem cbrW_ok (p : Prog) (L : CbrLook p) (n : Nat) : ∀ {m m' : Mem} {a : AState} {vis : Word} {fe : IFEnv}
    {vis2 pp mm lo ll : Word} {r : List Word} {bs : BlockShape} {xs : List (IConstantVal × TargetMajor × List EIdx)},
    cbrW p n m vis2 pp mm lo ll vis = some (r, m') → StageR dn vis fe m a →
    DecB (fun m => decBS m pp.toNat) m bs → PSlR decRR xs lo ll m → mm.toNat + ll.toNat < 2 ^ 64 →
    AbsOK m →
    ∃ fe' a', (ConRon.Arena.consBlockRecsTF vis2.toNat bs mm.toNat xs fe).run a = .ok (fe', a') ∧
      StageR dn (r.headD 0) fe' m' a' ∧ IWGrow m m' ∧ AbsOK m' := by
  induction n with
  | zero => intro m m' a vis fe vis2 pp mm lo ll r bs xs h; simp [cbrW] at h
  | succ n ih =>
  intro m m' a vis fe vis2 pp mm lo ll r bs xs h hS hbs hxs hml hA
  by_cases hl : ll = 0
  · rw [cbrW_nil (h := hl)] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    subst hl
    have : xs = [] := by
      have := decPL_length _ (hxs.1.get (OMono.decPL decRR_mono _ _)); simpa using this
    subst this
    exact ⟨fe, a, rfl, hS, IWGrow.refl _, hA⟩
  rw [cbrW_cons (h := hl)] at h
  have hsz := hS.2.2.2.1
  obtain ⟨x, ys, rfl, hx, hys⟩ := hxs.uncons hl hsz
  obtain ⟨cvv, TM, rhss⟩ := x
  generalize hT : rdW (m.arr64 IW) lo = trip at h hx
  -- the record's fields
  have hx' : decRR (truncM m) trip.toNat = some (cvv, TM, rhss) := hx
  simp only [decRR, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hx'
  obtain ⟨cvp, hcvp, cv', hcv', mp, hmp, TM', hTM', rh', hrh', he⟩ := hx'
  simp only [Prod.mk.injEq] at he; obtain ⟨e1', e2', e3'⟩ := he
  rw [e1'] at hcv'; rw [e2'] at hTM'; rw [e3'] at hrh'
  obtain ⟨-, hcvpm⟩ := rec2IwN_trunc (i := trip.toNat + 0) (by simpa using hcvp)
  obtain ⟨e0, t0⟩ := rec2RdN (w := trip) (k := 0) hcvpm hsz
  obtain ⟨-, hmpm⟩ := rec2IwN_trunc hmp
  obtain ⟨e1, t1⟩ := rec2RdN (w := trip) (k := 1) hmpm hsz
  obtain ⟨o, l, ho, hl', hd⟩ := decAt_some hrh'
  obtain ⟨-, hom⟩ := rec2IwN_trunc ho
  obtain ⟨-, hlm⟩ := rec2IwN_trunc hl'
  obtain ⟨e2, t2⟩ := rec2RdN (w := trip) (k := 2) hom hsz
  obtain ⟨e3, t3⟩ := rec2RdN (w := trip) (k := 3) (by simpa [Nat.add_assoc] using hlm) hsz
  simp only [show UInt64.ofNat 0 = (0 : Word) from rfl, show UInt64.ofNat 1 = (1 : Word) from rfl,
    show UInt64.ofNat 2 = (2 : Word) from rfl, show UInt64.ofNat 3 = (3 : Word) from rfl, UInt64.add_zero] at e0 e1 e2 e3
  rw [e0, e1, e2, e3] at h
  have hM : DecB (fun m => decTM m (UInt64.ofNat mp : Word).toNat) m TM := by
    show decTM (truncM m) _ = some TM; rw [t1]; exact hTM'
  have hrh : DecB (fun m => decHL m (UInt64.ofNat o : Word).toNat (UInt64.ofNat l : Word).toNat) m rhss := by
    show decHL (truncM m) _ _ = some rhss; rw [t2, t3]; exact hd
  have hcvE : decCV (erecP m) (UInt64.ofNat cvp : Word).toNat = some cvv := by rw [t0]; exact decCVp_truncM hcv'
  obtain ⟨hmj, hrp⟩ := bmjW_rpW_eq (r := mm) hbs hsz
  -- the stored rules, at the constructors' view
  rcases h1 : tsrW n m vis2 (UInt64.ofNat cvp) (brpW m pp mm) (UInt64.ofNat mp) (UInt64.ofNat o) (UInt64.ofNat l) with _ | ⟨rr, m1⟩ <;> simp only [h1, cbrK1, reduceCtorEq] at h
  obtain ⟨rules, a1, run1, hd1, hb1, hS1, hg1, hA1⟩ := tsrW_ok dn (fe.restrictTo vis2.toNat) vis2 n h1
    (hS.restrict vis2) hM hrh hA (cvv := cvv)
  have hS1' : StageR dn vis fe m1 a1 := hS1.unrestrict hS.1.env.vis
  rw [hrp] at run1
  rcases h2 : cbpW p n m1 vis (UInt64.ofNat cvp) (bmjW m pp mm) (brpW m pp mm) (rr.headD 0) (rr.tail.headD 0) with _ | ⟨rv, m2⟩ <;> simp only [h2, cbrK2, reduceCtorEq] at h
  obtain ⟨hS2, hg2, hf2⟩ := cbpW_ok dn fe vis p L n h2 hS1' ((IWGrow.erecPExtR hg1).decCV hcvE) hd1 hb1
  rw [hmj, hrp] at hS2
  rcases h3 : cbrW p n m2 vis2 pp (mm + 1) (lo + 1) (ll - 1) (rv.headD 0) with _ | ⟨r3, m3⟩ <;> simp only [h3, cbrK3, reduceCtorEq] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  have hg12 := hg1.trans hg2
  have hl0 : ll.toNat ≠ 0 := fun e => hl (UInt64.toNat_inj.mp (by simpa using e))
  have hmm1 : (mm + 1).toNat = mm.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hll1 : (ll - 1).toNat = ll.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  obtain ⟨fe', a3, run3, hS3, hg3, hA3⟩ := ih h3 hS2 (hbs.grow (decBS_mono _) hg12)
    (hys.grow (fun q => decRR_mono q) hg12) (by rw [hmm1, hll1]; omega) (hf2 hA1)
  refine ⟨fe', a3, ?_, by simpa using hS3, hg12.trans hg3, hA3⟩
  rw [hmm1] at run3
  simp only [ConRon.Arena.consBlockRecsTF, StateT.run_bind, run1, except_ok_bind]
  exact run3

end rel

/-- **`cons_block_recs_tf` (with `cons_block_recs_push`, `rec_info_rec`, `rules_to_erec(_go)`,
`rule_copy`) refines `consBlockRecsTF`** (through `tgt_stored_rules`' stubs): the shape and the
family's `rec4` records decoded below the tops; the environment with the recursors at the returned
view. -/
@[refines ConRon.Arena.consBlockRecsTF]
theorem consBlockRecsTF_refines (p : Prog) (L : CbrLook p) (n : Nat) (s₀ : St) (a₀ : AState)
    (dn : NIdx → Option ConLeche.Name) (fe : IFEnv) (vis2 pp mm lo ll vis : Word) (bs : BlockShape)
    (xs : List (IConstantVal × TargetMajor × List EIdx)) (hS : StageR dn vis fe s₀.mem a₀)
    (hbs : DecB (fun m => decBS m pp.toNat) s₀.mem bs) (hxs : PSlR decRR xs lo ll s₀.mem)
    (hml : mm.toNat + ll.toNat < 2 ^ 64) (hA : AbsOK s₀.mem) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "cons_block_recs_tf" [vis2, pp, mm, lo, ll, vis]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (ConRon.Arena.consBlockRecsTF vis2.toNat bs mm.toNat xs fe) a₀ ∧
      StageR dn (r.headD 0) (AM.res (ConRon.Arena.consBlockRecsTF vis2.toNat bs mm.toNat xs fe) a₀) s'.mem
        (AM.st (ConRon.Arena.consBlockRecsTF vis2.toNat bs mm.toNat xs fe) a₀) ∧
      IWGrow s₀.mem s'.mem ∧ AbsOK s'.mem; ⊤⦄ := by
  refine triple_post (cbr_spec p L n s₀ vis2 pp mm lo ll vis) ?_
  rintro r s' ⟨hl', hm⟩
  obtain ⟨fe', a', run, hS', hg, hA'⟩ := cbrW_ok dn p L n hm hS hbs hxs hml hA
  obtain ⟨hok, hst, hres⟩ := AM.of_run_ok _ _ _ _ run
  exact ⟨hl', hok, by rw [hres, hst]; exact hS', hg, hA'⟩

end L.Ind
