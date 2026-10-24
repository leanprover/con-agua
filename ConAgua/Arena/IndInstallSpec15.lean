import ConAgua.Arena.IndInstallSpec14

/-!
# Refinements of `IndInstall`, part 15 (lane `indproofs2`, helper `install`): `checkBlockInds`

The formers' constants `cvTa₀ :: cvs.map (·.1)` (`check_block_inds_cv_tas`, `sl_cons`-built,
D18), `block_shape_with_sort` below the tops, then stage 1: the formers checked, agreed, consed.
-/

noncomputable section

set_option experimental.vcgen true
set_option linter.deprecated false

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

local notation "V" => ConLeche.CheckMode.verified

/-! ## `check_block_inds_cv_tas` -/

def icvgK2 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => some ([r.headD 0, r.tail.headD 0], m)

mutual
/-- **The model of `check_block_inds_cv_tas_go(s, l)`** at exec fuel `n`. -/
def icvgW (p : Prog) : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, s, l => if l = 0 then some ([0, 0], m) else icvgK1 p n s (icvgW p n m (s + 1) (l - 1))
def icvgK1 (p : Prog) (n : Nat) (s : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m) => icvgK2 (callW p n "sl_cons" [rdW (m.arr64 IW) (rdW (m.arr64 IW) s), r.headD 0,
      r.tail.headD 0] m)
end

section arms
variable (p : Prog) (n : Nat) (m : Mem) (s l : Word) (r : List Word)
theorem icvgW_zero : icvgW p 0 m s l = none := by simp [icvgW]
theorem icvgW_nil (h : l = 0) : icvgW p (n + 1) m s l = some ([0, 0], m) := by simp [icvgW, h]
theorem icvgW_cons (h : l ≠ 0) : icvgW p (n + 1) m s l = icvgK1 p n s (icvgW p n m (s + 1) (l - 1)) := by
  simp [icvgW, h]
theorem icvgK1_some : icvgK1 p n s (some (r, m)) = icvgK2 (callW p n "sl_cons"
    [rdW (m.arr64 IW) (rdW (m.arr64 IW) s), r.headD 0, r.tail.headD 0] m) := by simp [icvgK1]
theorem icvgK2_some : icvgK2 (some (r, m)) = some ([r.headD 0, r.tail.headD 0], m) := rfl
end arms
attribute [ind_grind] icvgW_nil icvgW_cons icvgK1_some icvgK2_some

theorem icvg_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
    (n : Nat) : ∀ (s₀ : St) (s l : Word),
    ⦃fun st => st = s₀⦄ invoke p (exec p n) "check_block_inds_cv_tas_go" [s, l]
    ⦃fun r s' => LocEq s' s₀ ∧ icvgW p n s₀.mem s l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ s l; rw [invoke_eq _ hp]; simp only [callFn, checkBlockIndsCvTasGo]
    vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ s l
    rw [invoke_eq _ hp]
    simp only [callFn, checkBlockIndsCvTasGo]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, callW_spec p n "sl_cons", ih] <;>
      finish (gen := 20) [rdW_eq]

/-- The model of `check_block_inds_cv_tas(c0, o, l)` (body fuel `n`). -/
def icvW (p : Prog) (n : Nat) (m : Mem) (c0 o l : Word) : Option (List Word × Mem) :=
  match callW p n "check_block_inds_cv_tas_go" [o, l] m with
  | none => none
  | some (r, m1) => icvgK2 (callW p n "sl_cons" [c0, r.headD 0, r.tail.headD 0] m1)

theorem icv_spec (p : Prog) (hp : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas)
    (n : Nat) (s₀ : St) (c0 o l : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_inds_cv_tas" [c0, o, l]
    ⦃fun r s' => LocEq s' s₀ ∧ icvW p n s₀.mem c0 o l = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockIndsCvTas]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_block_inds_cv_tas_go", callW_spec p n "sl_cons"] <;>
    finish (gen := 20) [icvW, rdW_eq]

/-- `sl_cons`' run under the stage relation. -/
theorem installConsRun {p : Prog} (hP : CstProg p) {n : Nat} {α : Type} {f : Mem → Nat → Option α}
    (hf : ∀ q, OMono (fun m => f m q)) {dn : NIdx → Option ConLeche.Name} {vis : Word} {fe : IFEnv}
    {a : AState} {m m' : Mem} {x o l : Word} {r : List Word} {xs : List α} {y : α}
    (h : callW p n "sl_cons" [x, o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hxs : PSlR f xs o l m) (hy : DecB (fun m => f m x.toNat) m y) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PSlR f (y :: xs) (r.headD 0) (r.tail.headD 0) m' := by
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (slCons_specW p hP.alloc hP.copy hP.cons n _ x o l) h
  obtain ⟨hS', hg, hd, htop⟩ := partsConsPL hf hW hS hxs.2 hxs.1 hy
  exact ⟨hS', hg, hd, Nat.le_of_eq htop⟩

/-- **`check_block_inds_cv_tas_go`'s model**: the constants of the `[cvTa, s]` records. -/
theorem icvgW_ok {p : Prog} (hP : CstProg p) {dn : NIdx → Option ConLeche.Name} {vis : Word}
    {fe : IFEnv} {a : AState} (n : Nat) : ∀ (m m' : Mem) (s l : Word) (r : List Word)
      (xs : List (IConstantVal × LIdx)),
    icvgW p n m s l = some (r, m') → StageR dn vis fe m a → PSlR decTele xs s l m →
    StageR dn vis fe m' a ∧ IWGrow m m' ∧ PSlR decCVp (xs.map (·.1)) (r.headD 0) (r.tail.headD 0) m' := by
  induction n with
  | zero => intro m m' s l r xs h; rw [icvgW_zero] at h; cases h
  | succ n ih =>
  intro m m' s l r xs h hS hxs
  by_cases hl : l = 0
  · rw [icvgW_nil p n m s l hl] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    have : xs = [] := by
      have h := hxs.1; simp only [DecB, hl] at h
      simpa [decPL] using h.symm
    subst this
    exact ⟨hS, IWGrow.refl m, PSlR.nil decCVp m⟩
  obtain ⟨q, x, rest, rfl, hw, hqb, hdx, hrest⟩ := partsPSl_cons hxs hl
  rw [icvgW_cons p n m s l hl] at h
  obtain ⟨⟨r1, m1⟩, h1, h⟩ := of_K h rfl; rw [icvgK1_some] at h
  obtain ⟨hS1, hg1, hd1⟩ := ih m m1 (s + 1) (l - 1) r1 rest h1 hS hrest
  obtain ⟨⟨r2, m2⟩, h2, h⟩ := of_K h rfl; rw [icvgK2_some] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  -- the record's first word
  have hT : iwTop m < 2 ^ 64 := (rdW (m.arr64 CTL) 200).toNat_lt
  have hlpos : 0 < l.toNat := Nat.pos_of_ne_zero fun h0 => hl (UInt64.toNat_inj.mp (by simpa using h0))
  have hsl : s.toNat < iwTop m := by have := hxs.2; omega
  have hw1 : rdW (m1.arr64 IW) s = UInt64.ofNat q := by rw [← hw]; simp only [rdW]; rw [hg1.2.2.1 _ hsl]
  have hq' : (UInt64.ofNat q : Word).toNat = q := UInt64.toNat_ofNat_of_lt' hqb
  have hdx' : decTele (truncM m) q = some x := hdx
  simp only [decTele, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at hdx'
  obtain ⟨c, hc, cv, hcv, sv, -, rfl⟩ := hdx'
  obtain ⟨hwc, hcb, hclt⟩ := partsIwRd hc (w := UInt64.ofNat q) hq'
  have hqlt : q < iwTop m := partsIwLt hc
  have hwc1 : rdW (m1.arr64 IW) (UInt64.ofNat q) = UInt64.ofNat c := by
    rw [← hwc]; simp only [rdW, hq']; rw [hg1.2.2.1 _ hqlt]
  rw [hw1, hwc1] at h2
  have hc' : (UInt64.ofNat c : Word).toNat = c := UInt64.toNat_ofNat_of_lt' hcb
  obtain ⟨hS2, hg2, hd2⟩ := installConsRun hP (fun q => OMono.decCVp q) h2 hS1 hd1
    (by rw [hc']; exact (show DecB (fun m => decCVp m c) m cv from hcv).grow (OMono.decCVp _) hg1)
  exact ⟨hS2, hg1.trans hg2, by simpa using hd2⟩

/-- `check_block_inds_cv_tas`' run: `c0 :: cvs.map (·.1)`, a slice of constants below the tops. -/
theorem installCvTasRun {p : Prog} (hP : CstProg p) {n : Nat} {dn : NIdx → Option ConLeche.Name}
    {vis : Word} {fe : IFEnv} {a : AState} {m m' : Mem} {c0 o l : Word} {r : List Word}
    {cv0 : IConstantVal} {cvs : List (IConstantVal × LIdx)}
    (hcv : p.lookup "check_block_inds_cv_tas" = some checkBlockIndsCvTas)
    (hcg : p.lookup "check_block_inds_cv_tas_go" = some checkBlockIndsCvTasGo)
    (h : callW p n "check_block_inds_cv_tas" [c0, o, l] m = some (r, m')) (hS : StageR dn vis fe m a)
    (hc0 : DecB (fun m => decCVp m c0.toNat) m cv0) (hcvs : PSlR decTele cvs o l m) :
    StageR dn vis fe m' a ∧ IWGrow m m' ∧
      PSlR decCVp (cv0 :: cvs.map (·.1)) (r.headD 0) (r.tail.headD 0) m' := by
  rcases n with _ | n
  · rw [callW_zero] at h; cases h
  obtain ⟨s', rfl, -, hW⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (icv_spec p hcv n _ c0 o l) h
  simp only [icvW] at hW
  split at hW
  · cases hW
  rename_i r1 m1 h1
  obtain ⟨s1, rfl, -, hW1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩) (icvg_spec p hcg n _ o l) h1
  obtain ⟨hS1, hg1, hd1⟩ := icvgW_ok hP n _ _ o l r1 cvs hW1 hS hcvs
  obtain ⟨⟨r2, m2⟩, h2, hW⟩ := of_K hW rfl; rw [icvgK2_some] at hW
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hW)
  obtain ⟨hS2, hg2, hd2⟩ := installConsRun hP (fun q => OMono.decCVp q) h2 hS1 hd1
    (hc0.grow (OMono.decCVp _) hg1)
  exact ⟨hS2, hg1.trans hg2, by simpa using hd2⟩

/-- The recursor shapes' slice of the shape at `pp` lies below the top. -/
def RecsB (m : Mem) (pp : Word) : Prop :=
  ∀ o l, iwN m (pp.toNat + 2) = some o → iwN m (pp.toNat + 3) = some l → o + l ≤ iwTop m

theorem RecsB.grow {m m' : Mem} {pp : Word} (h : RecsB m pp) (hg : IWGrow m m') (h3 : pp.toNat + 3 < iwTop m) :
    RecsB m' pp := by
  intro o l ho hl
  rw [iwN_grow hg (by omega)] at ho
  rw [iwN_grow hg h3] at hl
  exact Nat.le_trans (h o l ho hl) hg.1

/-- Every member's former constant record lies below the tops (`CVExt`). -/
def ShapeCV (m : Mem) (q : Word) : Prop :=
  ∀ o l, iwN m q.toNat = some o → iwN m (q.toNat + 1) = some l → ∀ j < l, ∀ c,
    iwN m (o + j) = some c → ∀ d, iwN m c = some d → CVExt m d

/-! ## `check_block_inds` -/

def ibiK6 (r4 r5 : List Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r6, m6) => some ([r6.headD 0, r5.headD 0, r5.tail.headD 0, r4.headD 0], m6)
def ibiK5 (p : Prog) (n : Nat) (vis isRec : Word) (r4 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r5, m5) => ibiK6 r4 r5 (callW p n "cons_block_inds"
      [r4.headD 0, isRec, r5.headD 0, r5.tail.headD 0, vis, 0] m5)
def ibiK4 (p : Prog) (n : Nat) (vis isRec : Word) (r1 r2 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r4, m4) => ibiK5 p n vis isRec r4 (callW p n "check_block_inds_cv_tas"
      [r1.headD 0, r2.headD 0, r2.tail.headD 0] m4)
def ibiK3 (p : Prog) (n : Nat) (vis pp isRec : Word) (r1 r2 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (_, m3) => ibiK4 p n vis isRec r1 r2 (callW p n "block_shape_with_sort" [pp, r1.tail.headD 0] m3)
def ibiK2 (p : Prog) (n : Nat) (vis pp isRec nP : Word) (r1 : List Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) => ibiK3 p n vis pp isRec r1 r2 (callW p n "check_block_agree"
      [vis, nP, r1.headD 0, r1.tail.headD 0, r2.headD 0, r2.tail.headD 0] m2)
def ibiK1 (p : Prog) (n : Nat) (vis pp isRec nP moff mlen : Word) :
    Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r1, m1) => ibiK2 p n vis pp isRec nP r1 (callW p n "check_block_teles"
      [vis, nP, moff + 1, mlen - 1] m1)

/-- **The model of `check_block_inds(vis, p, is_rec)`** (body fuel `n`). -/
def ibiW (p : Prog) (n : Nat) (m : Mem) (vis pp isRec : Word) : Option (List Word × Mem) :=
  if rdW (m.arr64 IW) (pp + 1) = 0 then none
  else ibiK1 p n vis pp isRec (rdW (m.arr64 IW) (pp + 4)) (rdW (m.arr64 IW) pp) (rdW (m.arr64 IW) (pp + 1))
    (callW p n "check_block_tele" [vis, rdW (m.arr64 IW) (pp + 4), rdW (m.arr64 IW) (rdW (m.arr64 IW) pp)] m)

section arms
variable (p : Prog) (n : Nat) (m : Mem) (vis pp isRec nP moff mlen : Word) (r r1 r2 r4 r5 : List Word)
theorem ibiK6_some : ibiK6 r4 r5 (some (r, m)) = some ([r.headD 0, r5.headD 0, r5.tail.headD 0, r4.headD 0], m) := rfl
theorem ibiK5_some : ibiK5 p n vis isRec r4 (some (r, m)) = ibiK6 r4 r (callW p n "cons_block_inds"
    [r4.headD 0, isRec, r.headD 0, r.tail.headD 0, vis, 0] m) := rfl
theorem ibiK4_some : ibiK4 p n vis isRec r1 r2 (some (r, m)) = ibiK5 p n vis isRec r
    (callW p n "check_block_inds_cv_tas" [r1.headD 0, r2.headD 0, r2.tail.headD 0] m) := rfl
theorem ibiK3_some : ibiK3 p n vis pp isRec r1 r2 (some (r, m)) = ibiK4 p n vis isRec r1 r2
    (callW p n "block_shape_with_sort" [pp, r1.tail.headD 0] m) := rfl
theorem ibiK2_some : ibiK2 p n vis pp isRec nP r1 (some (r, m)) = ibiK3 p n vis pp isRec r1 r
    (callW p n "check_block_agree" [vis, nP, r1.headD 0, r1.tail.headD 0, r.headD 0, r.tail.headD 0] m) := rfl
theorem ibiK1_some : ibiK1 p n vis pp isRec nP moff mlen (some (r, m)) = ibiK2 p n vis pp isRec nP r
    (callW p n "check_block_teles" [vis, nP, moff + 1, mlen - 1] m) := rfl
end arms
attribute [ind_grind] ibiK6_some ibiK5_some ibiK4_some ibiK3_some ibiK2_some ibiK1_some

set_option maxHeartbeats 1600000 in
theorem ibi_spec (p : Prog) (hp : p.lookup "check_block_inds" = some checkBlockInds) (n : Nat)
    (s₀ : St) (vis pp isRec : Word) :
    ⦃fun st => st = s₀⦄ invoke p (exec p (n + 1)) "check_block_inds" [vis, pp, isRec]
    ⦃fun r s' => LocEq s' s₀ ∧ ibiW p n s₀.mem vis pp isRec = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, checkBlockInds]
  sym only [lang_grind, arena_grind, ind_grind] =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      callW_spec p n "check_block_tele", callW_spec p n "check_block_teles",
      callW_spec p n "check_block_agree", callW_spec p n "block_shape_with_sort",
      callW_spec p n "check_block_inds_cv_tas", callW_spec p n "cons_block_inds"] <;>
    finish (gen := 40) (instances := 20000) [ibiW, rdW_eq]

end L.Ind
