import ConAgua.Arena.IndSim
import ConAgua.Arena.IndDecStab
import ConAgua.Arena.IndPartsSpec6
import ConAgua.Arena.IndPosSpec2A
import ConAgua.Arena.RecClassSpecA

/-!
# Refinements of `IndParts`, part 7 (lane `indproofs2`, helper `parts`): the block split

`blockSplitRecs`, `blockSplitCtors`, `blockSplit`: pure `Option` twins over the block (an `EREC`
slice of constant-record pointers, `decEBlk`). The L functions recurse as the twins do (the rest
first, then a fresh element record consed on with `sl_cons`), so each relational lemma is one fuel
induction mirroring the twin's equations. Results are decoded below the tops (`DecB`), so they
stay decoded across every later growth of the pools.

Element decoders: `decSR` (`[cv, mI, rP, rules.off, rules.len]`, the rules an `EREC` slice of
`decRule` records), `decSC` (`[cv, nP, nF]`), `decSplit` (`blockSplit`'s 6-word record).
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Decoders of the split's records -/

/-- `blockSplitRecs`'s element `[cv, mI, rP, rules.off, rules.len]`. -/
def decSR (m : Mem) (p : Nat) : Option (IConstantVal × Nat × Nat × List IRecRule) := do
  pure (← decCVp m (← iwN m p), ← iwN m (p + 1), ← iwN m (p + 2),
    ← decRules (erA m) (← iwN m (p + 3)) (← iwN m (p + 4)))

/-- `blockSplitCtors`'s element `[cv, nP, nF]`. -/
def decSC (m : Mem) (p : Nat) : Option (IConstantVal × Nat × Nat) := do
  pure (← decCVp m (← iwN m p), ← iwN m (p + 1), ← iwN m (p + 2))

theorem partsDecRules_mono (o l : Nat) : OMono (fun m => decRules (erA m) o l) :=
  ⟨fun _ _ _ he h => he.2.decRules h⟩

theorem decSR_mono (p : Nat) : OMono (fun m => decSR m p) := by
  unfold decSR
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decCVp
    | apply partsDecRules_mono
    | apply OMono.bind
    | intro _)

theorem decSC_mono (p : Nat) : OMono (fun m => decSC m p) := by
  unfold decSC
  repeat' (first
    | exact OMono.const _
    | apply OMono.iwN
    | apply OMono.decCVp
    | apply OMono.bind
    | intro _)

/-! ## `rec3` as `posRecW` -/

theorem partsRec3_eq (m : Mem) (a b c : Word) :
    (match allocW m 3 with | none => none | some (q, _) => some (q, rec3Mem m a b c)) =
      posRecW m [a, b, c] := by
  rw [posRecW_eq m [a, b, c] 3 rfl, rec3Mem_eq]; cases allocW m 3 <;> rfl

theorem partsRec3_specW (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (h3 : p.lookup "rec3" = some rec3) (n : Nat) (s₀ : St) (a b c : Word) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "rec3" [a, b, c]
    ⦃fun r s' => LocEq s' s₀ ∧ posRecW s₀.mem [a, b, c] = some (r.headD 0, s'.mem); ⊤⦄ := by
  rw [← partsRec3_eq, invoke_eq _ h3]
  simp only [callFn, rec3]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        iwAlloc_specW p ha n] <;>
      finish [rec3Mem, allocMem, allocW]

/-! ## The word models -/

/-- After `sl_cons`: the result triple. -/
def bsK3 : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m3) => some ([1, r2.headD 0, r2.tail.headD 0], m3)

/-- `block_split_recs` after the element record: `sl_cons` onto the rest `r`. -/
def bsrK2 (n : Nat) (r : List Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (rc, m2) => bsK3 (consW n m2 rc (r.tail.headD 0) (r.tail.tail.headD 0))

/-- `block_split_recs` after the recursive call. -/
def bsrK1 (n : Nat) (ci : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0], m1)
    else bsrK2 n r (posRecW m1 [ci + 1, rdW (m1.arr64 EREC) (ci + 5), rdW (m1.arr64 EREC) (ci + 6),
      rdW (m1.arr64 EREC) (ci + 7), rdW (m1.arr64 EREC) (ci + 8)])

/-- **The model of `block_split_recs`.** -/
def bsrW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, off, l =>
    if l = 0 then some ([1, 0, 0], m)
    else if rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 5 then some ([0, 0, 0], m)
    else bsrK1 n (rdW (m.arr64 EREC) off) (bsrW n m (off + 1) (l - 1))

section arms
variable (n : Nat) (m m1 m2 : Mem) (off l ci rc : Word) (r r2 : List Word)
theorem bsrW_nil (h : l = 0) : bsrW (n + 1) m off l = some ([1, 0, 0], m) := by simp [bsrW, h]
theorem bsrW_no (h : l ≠ 0) (h5 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 5) :
    bsrW (n + 1) m off l = some ([0, 0, 0], m) := by simp [bsrW, h, h5]
theorem bsrW_rec (h : l ≠ 0) (h5 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 5) :
    bsrW (n + 1) m off l = bsrK1 n (rdW (m.arr64 EREC) off) (bsrW n m (off + 1) (l - 1)) := by
  simp [bsrW, h, h5]
theorem bsrK1_fail (h : r.headD 0 = 0) : bsrK1 n ci (some (r, m1)) = some ([0, 0, 0], m1) := by
  simp only [bsrK1]; rw [if_pos h]
theorem bsrK1_ok (h : r.headD 0 ≠ 0) : bsrK1 n ci (some (r, m1)) =
    bsrK2 n r (posRecW m1 [ci + 1, rdW (m1.arr64 EREC) (ci + 5), rdW (m1.arr64 EREC) (ci + 6),
      rdW (m1.arr64 EREC) (ci + 7), rdW (m1.arr64 EREC) (ci + 8)]) := by
  simp only [bsrK1]; exact if_neg (c := r.headD 0 = 0) h
theorem bsrK2_some : bsrK2 n r (some (rc, m2)) =
    bsK3 (consW n m2 rc (r.tail.headD 0) (r.tail.tail.headD 0)) := rfl
theorem bsK3_some : bsK3 (some (r2, m2)) = some ([1, r2.headD 0, r2.tail.headD 0], m2) := rfl
end arms
attribute [ind_grind] bsrW_nil bsrW_no bsrW_rec bsrK1_fail bsrK1_ok bsrK2_some bsK3_some

/-- `block_split_ctors` after the element record. -/
def bscK2 (n : Nat) (r : List Word) : Option (Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (c, m2) =>
    match consW n m2 c (r.tail.headD 0) (r.tail.tail.headD 0) with
    | none => none
    | some (r2, m3) => some ([1, r2.headD 0, r2.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], m3)

/-- `block_split_ctors` after the recursive call. -/
def bscK1 (n : Nat) (ci : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else bscK2 n r (posRecW m1 [ci + 1, rdW (m1.arr64 EREC) (ci + 5), rdW (m1.arr64 EREC) (ci + 6)])

/-- `block_split_ctors` after `block_split_recs`. -/
def bscKR : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0, 0, 0, 0], m1)
    else some ([1, 0, 0, r.tail.headD 0, r.tail.tail.headD 0], m1)

/-- **The model of `block_split_ctors`.** -/
def bscW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, off, l =>
    if l = 0 then some ([1, 0, 0, 0, 0], m)
    else if rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 4 then bscKR (bsrW n m off l)
    else bscK1 n (rdW (m.arr64 EREC) off) (bscW n m (off + 1) (l - 1))

section arms
variable (n : Nat) (m m1 m2 : Mem) (off l ci c : Word) (r : List Word)
theorem bscW_nil (h : l = 0) : bscW (n + 1) m off l = some ([1, 0, 0, 0, 0], m) := by simp [bscW, h]
theorem bscW_no (h : l ≠ 0) (h4 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 4) :
    bscW (n + 1) m off l = bscKR (bsrW n m off l) := by simp [bscW, h, h4]
theorem bscW_ctor (h : l ≠ 0) (h4 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 4) :
    bscW (n + 1) m off l = bscK1 n (rdW (m.arr64 EREC) off) (bscW n m (off + 1) (l - 1)) := by
  simp [bscW, h, h4]
theorem bscKR_fail (h : r.headD 0 = 0) : bscKR (some (r, m1)) = some ([0, 0, 0, 0, 0], m1) := by
  simp only [bscKR]; rw [if_pos h]
theorem bscKR_ok (h : r.headD 0 ≠ 0) :
    bscKR (some (r, m1)) = some ([1, 0, 0, r.tail.headD 0, r.tail.tail.headD 0], m1) := by
  simp only [bscKR]; exact if_neg (c := r.headD 0 = 0) h
theorem bscK1_fail (h : r.headD 0 = 0) : bscK1 n ci (some (r, m1)) = some ([0, 0, 0, 0, 0], m1) := by
  simp only [bscK1]; rw [if_pos h]
theorem bscK1_ok (h : r.headD 0 ≠ 0) : bscK1 n ci (some (r, m1)) =
    bscK2 n r (posRecW m1 [ci + 1, rdW (m1.arr64 EREC) (ci + 5), rdW (m1.arr64 EREC) (ci + 6)]) := by
  simp only [bscK1]; exact if_neg (c := r.headD 0 = 0) h
theorem bscK2_some : bscK2 n r (some (c, m2)) =
    (match consW n m2 c (r.tail.headD 0) (r.tail.tail.headD 0) with
    | none => none
    | some (r2, m3) => some ([1, r2.headD 0, r2.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0], m3)) := rfl
end arms
attribute [ind_grind] bscW_nil bscW_no bscW_ctor bscKR_fail bscKR_ok bscK1_fail bscK1_ok bscK2_some

/-- `block_split` after `block_split_ctors`. -/
def bsKC : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0], m1)
    else match posRecW m1 [0, 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0] with
      | none => none
      | some (q, m2) => some ([1, q], m2)

/-- `block_split` after `sl_cons`: the new record. -/
def bsK2 (q : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r2, m2) =>
    match posRecW m2 [r2.headD 0, r2.tail.headD 0, rdW (m2.arr64 IW) (q + 2), rdW (m2.arr64 IW) (q + 3),
        rdW (m2.arr64 IW) (q + 4), rdW (m2.arr64 IW) (q + 5)] with
    | none => none
    | some (q2, m3) => some ([1, q2], m3)

/-- `block_split` after the recursive call. -/
def bsK1 (n : Nat) (ci : Word) : Option (List Word × Mem) → Option (List Word × Mem)
  | none => none
  | some (r, m1) =>
    if r.headD 0 = 0 then some ([0, 0], m1)
    else bsK2 (r.tail.headD 0) (consW n m1 (ci + 1) (rdW (m1.arr64 IW) (r.tail.headD 0))
      (rdW (m1.arr64 IW) (r.tail.headD 0 + 1)))

/-- **The model of `block_split`.** -/
def bsW : Nat → Mem → Word → Word → Option (List Word × Mem)
  | 0, _, _, _ => none
  | n + 1, m, off, l =>
    if l = 0 then
      (match posRecW m [0, 0, 0, 0, 0, 0] with
       | none => none
       | some (q, m1) => some ([1, q], m1))
    else if rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 3 then bsKC (bscW n m off l)
    else bsK1 n (rdW (m.arr64 EREC) off) (bsW n m (off + 1) (l - 1))

section arms
variable (n : Nat) (m m1 m2 : Mem) (off l ci q : Word) (r : List Word)
theorem bsW_nil (h : l = 0) : bsW (n + 1) m off l = (match posRecW m [0, 0, 0, 0, 0, 0] with
    | none => none
    | some (q, m1) => some ([1, q], m1)) := by simp [bsW, h]
theorem bsW_no (h : l ≠ 0) (h3 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) ≠ 3) :
    bsW (n + 1) m off l = bsKC (bscW n m off l) := by simp [bsW, h, h3]
theorem bsW_ind (h : l ≠ 0) (h3 : rdW (m.arr64 EREC) (rdW (m.arr64 EREC) off) = 3) :
    bsW (n + 1) m off l = bsK1 n (rdW (m.arr64 EREC) off) (bsW n m (off + 1) (l - 1)) := by
  simp [bsW, h, h3]
theorem bsKC_fail (h : r.headD 0 = 0) : bsKC (some (r, m1)) = some ([0, 0], m1) := by simp only [bsKC]; rw [if_pos h]
theorem bsKC_ok (h : r.headD 0 ≠ 0) : bsKC (some (r, m1)) =
    (match posRecW m1 [0, 0, r.tail.headD 0, r.tail.tail.headD 0, r.tail.tail.tail.headD 0,
        r.tail.tail.tail.tail.headD 0] with
      | none => none
      | some (q, m2) => some ([1, q], m2)) := by
  simp only [bsKC]; exact if_neg (c := r.headD 0 = 0) h
theorem bsK1_fail (h : r.headD 0 = 0) : bsK1 n ci (some (r, m1)) = some ([0, 0], m1) := by
  simp only [bsK1]; rw [if_pos h]
theorem bsK1_ok (h : r.headD 0 ≠ 0) : bsK1 n ci (some (r, m1)) =
    bsK2 (r.tail.headD 0) (consW n m1 (ci + 1) (rdW (m1.arr64 IW) (r.tail.headD 0))
      (rdW (m1.arr64 IW) (r.tail.headD 0 + 1))) := by
  simp only [bsK1]; exact if_neg (c := r.headD 0 = 0) h
theorem bsK2_some : bsK2 q (some (r, m2)) =
    (match posRecW m2 [r.headD 0, r.tail.headD 0, rdW (m2.arr64 IW) (q + 2), rdW (m2.arr64 IW) (q + 3),
        rdW (m2.arr64 IW) (q + 4), rdW (m2.arr64 IW) (q + 5)] with
    | none => none
    | some (q2, m3) => some ([1, q2], m3)) := rfl
end arms
attribute [ind_grind] bsW_nil bsW_no bsW_ind bsKC_fail bsKC_ok bsK1_fail bsK1_ok bsK2_some

/-! ## The `vcgen` specs -/

section spec
variable (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc) (hc : p.lookup "iw_copy" = some iwCopy)
  (hs : p.lookup "sl_cons" = some slCons)

include ha hc hs in
theorem bsr_spec (h5 : p.lookup "rec5" = some rec5)
    (hp : p.lookup "block_split_recs" = some blockSplitRecs) (n : Nat) : ∀ (s₀ : St) (off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split_recs" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bsrW n s₀.mem off l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off l; rw [invoke_eq _ hp]; simp only [callFn, blockSplitRecs]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off l
    rw [invoke_eq _ hp]
    simp only [callFn, blockSplitRecs]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        posRec5_specW p ha h5 n, slCons_specW p ha hc hs n, ih] <;> finish (gen := 20) [rdW_eq]

include ha hc hs in
theorem bsc_spec (h5 : p.lookup "rec5" = some rec5) (h3 : p.lookup "rec3" = some rec3)
    (hr : p.lookup "block_split_recs" = some blockSplitRecs)
    (hp : p.lookup "block_split_ctors" = some blockSplitCtors) (n : Nat) : ∀ (s₀ : St) (off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split_ctors" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bscW n s₀.mem off l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off l; rw [invoke_eq _ hp]; simp only [callFn, blockSplitCtors]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off l
    rw [invoke_eq _ hp]
    simp only [callFn, blockSplitCtors]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        partsRec3_specW p ha h3 n, slCons_specW p ha hc hs n, bsr_spec p ha hc hs h5 hr n, ih] <;>
      finish (gen := 20) [rdW_eq]

include ha hc hs in
theorem bs_spec (h5 : p.lookup "rec5" = some rec5) (h3 : p.lookup "rec3" = some rec3)
    (h6 : p.lookup "rec6" = some rec6)
    (hr : p.lookup "block_split_recs" = some blockSplitRecs)
    (hct : p.lookup "block_split_ctors" = some blockSplitCtors)
    (hp : p.lookup "block_split" = some blockSplit) (n : Nat) : ∀ (s₀ : St) (off l : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_split" [off, l]
    ⦃fun r s' => LocEq s' s₀ ∧ bsW n s₀.mem off l = some (r, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ off l; rw [invoke_eq _ hp]; simp only [callFn, blockSplit]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ off l
    rw [invoke_eq _ hp]
    simp only [callFn, blockSplit]
    sym only [lang_grind, arena_grind, ind_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
        rec6_specW p ha h6 n, slCons_specW p ha hc hs n, bsc_spec p ha hc hs h5 h3 hr hct n, ih] <;>
      finish (gen := 20) [rdW_eq]

end spec

end L.Ind
