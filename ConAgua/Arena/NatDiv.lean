module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatSub
meta import ConAgua.Arena.NatAdd
meta import ConAgua.Arena.NatDivWord
meta import ConAgua.Arena.NatDivSubmul
import ConAgua.Census.Attr
public import ConAgua.Arena.NatShiftFacts
public import ConAgua.Arena.NatSub
public import ConAgua.Arena.NatOff
public import ConAgua.Arena.NatDivSubmul
public import ConAgua.Arena.NatDivWord
import ConAgua.Arena.NatDivFacts
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve
import ConAgua.L.For

@[expose] public section

/-!
# `Nat.div`/`Nat.mod` on the limb pool: `nat_divmod`

`nat_divmod(oa, la, ob, lb)` is `(a / b, a % b)` for a normalised `b` (con-ron's `div_mod`,
`dm_run`, `dm_limbs`, `dm_step`, `dm_correct`, `ron/nat.rs:752-876`): long division one quotient
LIMB at a time from the top. L has no division instruction; the 2-by-1 word division is
`div_2by1` (`NatDivWord.lean`: Möller and Granlund's estimate with a reciprocal computed once per
call, made exact by two correction loops).

* `lb = 0` or `la < lb`: the quotient is `0` and the remainder `a`'s own slice, trimmed (Lean's
  `a / 0 = 0`, `a % 0 = a`).
* `lb = 1` (`d1Loop`): con-ron's one-limb case, one `div_2by1` per limb of `a`, the remainder in a
  word. The divisor is normalised (`d = b · 2^s`, top bit set) and the dividend's limbs are read
  shifted on the fly, so the remainder is kept as `r · 2^s`.
* `lb ≥ 2` (`dkLoop`, `div_kstep`): Knuth's algorithm D on a copy of `a` with one zero limb on
  top (the work region at `w`, after the `la - lb + 1` quotient limbs at `top`). Step `j` works on
  the window `w[j ‥ j + lb]`, which holds `rem · 2^64 + a[j]` for the remainder `rem < b` of the
  limbs above: the estimate `q̂ = min(⌊U / D⌋, 2^64 - 1)` from the window's top two words and `b`'s
  top word, both read shifted left by `s` (so `D` is normalised, as con-ron normalises both
  operands, but without copies); `div_submul` subtracts `q̂ · b` from the window in place; and
  `div_add` adds `b` back while the window is negative, one decrement of `q̂` each (con-ron's
  `dm_correct`). The proof needs only `q̂ ≥ ⌊T / b⌋` (`knuth_est`, `NatDivFacts.lean`) and that a
  correction keeps it; Knuth's "at most two corrections" (a speed fact) is tested, not proved.

The in-place passes change only their region: `Off p q o n` (the pools agree off `[o, o + n)`)
is their frame, a named predicate with `grind` patterns, as `Agree` is for appending.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## The in-place passes -/

def daddLoop : Stmt := lblk (r, n, ob, lb, i, c, x, y, rt, rb) {
  for i < n {
    x := POOL⦃r + i⦄;
    y := call nat_limb(ob, lb, i);
    POOL⟨rt⟩[rb + i] := x + y + c;
    c := call add_carry(x, y, c)
  }
}

/-- `div_add(r, n, ob, lb)`: `R := R + b` in place (`b` zero-extended); returns the carry. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divAdd : FunDecl := lfn (r, n, ob, lb) locals (i, c, x, y, rt, rb) {
  rt := ⦃r⦄.tier;
  rb := ⦃r⦄.idx;
  ⟪daddLoop⟫;
  return c
}


section passes
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry) (P0 : Array Word) (C : Nat)

/-- The invariant of `div_add`'s pass. -/
def DAddInv (P0 : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 64 ∧ P0.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ C ∧ (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 0).toNat ∧
  s.loc 8 = s.loc 0 >>> 40 ∧ s.loc 9 = s.loc 0 &&& 1099511627775 ∧
  (s.mem.arr64 (tierA POOL (s.loc 8))).size ≤ 2 ^ 40 ∧ (s.loc 8).toNat ≤ 1 ∧ (s.loc 0).toNat < 2 ^ 41 ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧ (s.loc 5).toNat ≤ 1 ∧
  Off (vpool s.mem) P0 (s.loc 0).toNat (s.loc 4).toNat ∧
  pv (vpool s.mem) (s.loc 0).toNat (s.loc 4).toNat + (s.loc 5).toNat * wt (s.loc 4).toNat =
    pv P0 (s.loc 0).toNat (s.loc 4).toNat + xv P0 (s.loc 2).toNat (s.loc 3).toNat (s.loc 4).toNat

def DAddPost (P0 : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  (s'.loc 5).toNat ≤ 1 ∧ Off (vpool s'.mem) P0 (s₀.loc 0).toNat (s₀.loc 1).toNat ∧
  pv (vpool s'.mem) (s₀.loc 0).toNat (s₀.loc 1).toNat + (s'.loc 5).toNat * wt (s₀.loc 1).toNat =
    pv P0 (s₀.loc 0).toNat (s₀.loc 1).toNat + xv P0 (s₀.loc 2).toNat (s₀.loc 3).toNat (s₀.loc 1).toNat

-- the virtual pool's extra `P0.size` conjunct pushes the step past the default budget
set_option maxHeartbeats 2000000 in
include hpl hpc in
theorem daddLoop_spec (n : Nat) (s₀ : St) (h : DAddInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ exec p n daddLoop ⦃fun r s' => DAddPost P0 C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [DAddInv, DAddPost] at h ⊢
    rw [exec, step_while (w := daddLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, natLimb_spec p hpl n,
      addCarry_spec p hpc n]
    all_goals clear ih
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals grind (splits := 20) [arena_grind, lang_grind, DAddInv, DAddPost]

include hpl hpc in
theorem daddLoop_step_spec (n : Nat) (s₀ : St) (h : DAddInv P0 C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) daddLoop ⦃fun r s' => DAddPost P0 C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (daddLoop_spec p hpl hpc P0 C (n + 1) s₀ h)

end passes

section passFns
variable (p : Prog) (hpl : p.lookup "nat_limb" = some natLimb)
  (hpc : p.lookup "add_carry" = some addCarry)

include hpl hpc in
theorem divAdd_spec (hp : p.lookup "div_add" = some divAdd) (n : Nat) (s₀ : St)
    (r k ob lb : Word) (hs : pcap s₀.mem < 2 ^ 64)
    (hr : r.toNat + k.toNat ≤ pcap s₀.mem) (hb : ob.toNat + lb.toNat ≤ r.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_add" [r, k, ob, lb]
    ⦃fun res s' => LocEq s' s₀ ∧ PFrame s₀.mem s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧ (res.headD 0).toNat ≤ 1 ∧
      Off (vpool s'.mem) (vpool s₀.mem) r.toNat k.toNat ∧
      pv (vpool s'.mem) r.toNat k.toNat + (res.headD 0).toNat * wt k.toNat =
        pv (vpool s₀.mem) r.toNat k.toNat + xv (vpool s₀.mem) ob.toNat lb.toNat k.toNat; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, divAdd]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalArgs, setLoc,
        daddLoop_step_spec p hpl hpc (vpool s₀.mem) (pcap s₀.mem) n] <;>
      finish [DAddInv, DAddPost]

end passFns

/-! ## Arithmetic of the long division -/

theorem Agree.of_off (p q r : Array Word) (o k t : Nat) (h : Off p q o k) (h' : Agree q r t)
    (ht : t ≤ o) : Agree p r t := fun j hj => (h j (Or.inl (by omega))).trans (h' j hj)
grind_pattern [arena_grind] Agree.of_off => Off p q o k, Agree q r t

/-- Prepending a limb: `pv p o (k + 1) = p[o] + 2^64 · pv p (o + 1) k`. -/
theorem pv_cons (p : Array Word) (o o' k k' : Nat) (ho : o' = o + 1) (hk : k' = k + 1)
    (h : o < p.size) : pv p o k' = p[o].toNat + 2 ^ 64 * pv p o' k := by
  subst ho hk
  have := pv_append p o 1 k
  rw [Nat.add_comm 1 k] at this
  rw [this, pv_one p o h]; rfl
grind_pattern [natop_grind] pv_cons => pv p o k', pv p o' k, p[o]

/-- Writing a limb just below a slice of an in-place region's other side (`Off`), and prepending
it: the slice is read in the pool before the pass. -/
theorem pv_set_cons_off (p q : Array Word) (o o' k k' j r n : Nat) (v : Word) (hoff : Off p q r n)
    (hj : j = o) (ho : o' = o + 1) (hk : k' = k + 1) (hd : o + k' ≤ r) (h : o < p.size) :
    pv (p.set! j v) o k' = v.toNat + 2 ^ 64 * pv q o' k := by
  subst j
  have hs : o < (p.set! o v).size := by simpa using h
  have hc := pv_cons (p.set! o v) o o' k k' ho hk hs
  rw [hc]
  have h1 : pv (p.set! o v) o' k = pv p o' k := by
    subst ho
    clear hk hc hd
    induction k with
    | zero => rfl
    | succ k ih =>
      simp only [pv, ih]
      rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
      simp [show o ≠ o + 1 + k by omega]
  rw [h1, Off.pv_below p q r n o' k hoff (by omega)]
  simp [Array.set!_eq_setIfInBounds]
grind_pattern [natop_grind] pv_set_cons_off => pv (p.set! j v) o k', Off p q r n, pv q o' k

theorem pv_pos_of_norm (p : Array Word) (o l : Nat) (hn : Norm p o l) (hl : 0 < l) :
    0 < pv p o l := Nat.lt_of_lt_of_le (wt_pos _) (pv_ge_wt p o l hl hn)
grind_pattern [arena_grind] pv_pos_of_norm => Norm p o l, pv p o l

/-- The quotient and the remainder from `A = Q · B + R`, `R < B` (bounds on `Q · B` only, so
that the pattern binds every variable). -/
theorem div_of_bounds (A B Q : Nat) (h1 : Q * B ≤ A) (h2 : A < Q * B + B) : A / B = Q := by
  apply Nat.div_eq_of_lt_le
  · exact h1
  · rw [Nat.succ_mul]; exact h2
grind_pattern [natcmp_grind] div_of_bounds => A / B, Q * B

theorem mod_of_bounds (A B Q : Nat) (h1 : Q * B ≤ A) (h2 : A < Q * B + B) :
    A % B = A - Q * B := by
  have := Nat.div_add_mod A B
  rw [div_of_bounds A B Q h1 h2] at this
  rw [Nat.mul_comm] at this; omega
grind_pattern [natcmp_grind] mod_of_bounds => A % B, Q * B

/-- Writing below a slice does not change it. -/
theorem pv_set_below (p : Array Word) (o k j : Nat) (v : Word) (h : j < o) :
    pv (p.set! j v) o k = pv p o k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [pv, ih]
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [show j ≠ o + k by omega]
grind_pattern [arena_grind] pv_set_below => pv (p.set! j v) o k

/-- The limb loop's exit: the pointer is back at the slice's start, all limbs done. -/
theorem pv_exit (p : Array Word) (pa oa : Nat) (i la : Word) (h : ¬ i < la)
    (hi : i.toNat ≤ la.toNat) (hpa : pa + i.toNat = oa + la.toNat) :
    pv p pa i.toNat = pv p oa la.toNat := by
  have : i.toNat = la.toNat := by
    have : ¬ i.toNat < la.toNat := fun h' => h (UInt64.lt_iff_toNat_lt.mpr h')
    omega
  rw [this, show pa = oa by omega]
grind_pattern [natop_grind] pv_exit => pv p pa i.toNat, pv p oa la.toNat, i < la

theorem Grows.refl (m : Mem) (h : PoolOK m) : Grows m m := by
  have h2 := h.ctl
  have hf : PFrame (m.set64 CTL 0 m.top) m := by
    refine ⟨by rw [Mem.bytes_set64], fun b _ _ => ?_,
      by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)],
      by rw [Mem.arr64_set64_ne _ _ _ _ _ (by decide)], rfl⟩
    by_cases hb : b = CTL
    · subst hb
      rw [Mem.arr64_set64_same, Mem.top_eq m h2]
      simp only [Array.set!_eq_setIfInBounds, show (0 : Word).toNat = 0 from rfl]
      grind
    · rw [Mem.arr64_set64_ne _ _ _ _ _ hb]
  exact Grows.intro m m h hf (Agree.refl _ _) (Nat.le_refl _) (by have := h.inTier; omega)
grind_pattern [arena_grind] Grows.refl => Grows m m

/-- A shorter prefix of a slice in use is in use. -/
theorem SliceOK.shrink {m : Mem} {o l l' : Word} (h : SliceOK m o l) (hl : l'.toNat ≤ l.toNat) :
    SliceOK m o l' := by
  obtain ⟨h1, h2⟩ := h
  exact ⟨by omega, by omega⟩
grind_pattern [arena_grind] SliceOK.shrink => SliceOK m o l, SliceOK m o l'

/-- A slice of what a pool function appended, `[top, top')`, is in use. -/
theorem SliceOK.sub {m m' : Mem} {o l : Word} (hg : Grows m m') (ho : m.top.toNat ≤ o.toNat)
    (hl : o.toNat + l.toNat ≤ m'.top.toNat) : SliceOK m' o l := by
  have ht := hg.tier
  exact ⟨hl, by omega⟩
grind_pattern [arena_grind] SliceOK.sub => Grows m m', SliceOK m' o l

/-- `Grows.write` for a new top `v` not of the form `top + n` (`nat_divmod`'s `ro + n`); its
pattern puts the `Grows` fact into a goal about the final memory (`PoolOK`, `SliceOK`). -/
theorem Grows.write_at (m m₂ : Mem) (v : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (hv : m.top.toNat ≤ v.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (v.toNat - m.top.toNat) ≤
      (m.arr64 (tierA POOL (m.top >>> 40))).size) :
    Grows m (m₂.set64 CTL 0 v) := by
  have hctl : 0 < (m₂.arr64 CTL).size := by rw [hf.ctl]; exact hok.ctl
  have htop : (m₂.set64 CTL 0 v).top = v := Mem.top_set64 _ _ hctl
  apply Grows.intro m _ hok
  · rw [htop]; exact PFrame.set64_both CTL 0 _ hf (by decide) (by decide)
  · rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩]; exact ha
  · rw [htop]; exact hv
  · rw [htop]; exact hk

/-- `Grows.write_at`'s pool invariant, keyed on the goal (a `Grows` pattern on `m₂.set64 CTL 0 v`
would fire on every frame `Grows.intro` builds). -/
theorem PoolOK.write_at (m m₂ : Mem) (v : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (hv : m.top.toNat ≤ v.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (v.toNat - m.top.toNat) ≤
      (m.arr64 (tierA POOL (m.top >>> 40))).size) :
    PoolOK (m₂.set64 CTL 0 v) := hok.grows (Grows.write_at m m₂ v hok hf ha hv hk)
grind_pattern [arena_grind] PoolOK.write_at => PoolOK m, PoolOK (m₂.set64 CTL 0 v)

/-- `Grows.write_at`'s fresh slices, keyed on the goal. -/
theorem SliceOK.write_at (m m₂ : Mem) (v o l : Word) (hok : PoolOK m) (hf : PFrame m m₂)
    (ha : Agree (vpool m₂) (vpool m) m.top.toNat) (hv : m.top.toNat ≤ v.toNat)
    (hk : (m.top &&& 1099511627775).toNat + (v.toNat - m.top.toNat) ≤
      (m.arr64 (tierA POOL (m.top >>> 40))).size)
    (ho : m.top.toNat ≤ o.toNat) (hl : o.toNat + l.toNat ≤ v.toNat) :
    SliceOK (m₂.set64 CTL 0 v) o l := by
  have hg := Grows.write_at m m₂ v hok hf ha hv hk
  have hctl : 0 < (m₂.arr64 CTL).size := by rw [hf.ctl]; exact hok.ctl
  exact SliceOK.sub hg ho (by rw [Mem.top_set64 _ _ hctl]; exact hl)
grind_pattern [arena_grind] SliceOK.write_at => PoolOK m, SliceOK (m₂.set64 CTL 0 v) o l

/-- The slice of length `0` at the top is in use. -/
theorem SliceOK.top0 {m : Mem} {o : Word} (h : o = m.top) : SliceOK m o 0 := by
  subst h; exact ⟨by simp, by omega⟩
grind_pattern [arena_grind] SliceOK.top0 => SliceOK m o 0


/-! ## `nat_divmod(oa, la, ob, lb)` -/

/-- The correction (con-ron's `dm_correct`): while the window is negative (`c` the borrow), one
decrement of `q` and one addition of `b`; the carry out of the addition ends it. -/
def dcLoop : Stmt := lblk (wj, lb, ob, s, d, v, x, c, q, u1, u0, r) {
  while c != 0 {
    q := q - 1;
    c := call div_add(wj, lb + 1, ob, lb);
    c := u64(c == 0)
  }
}

/-- `div_kstep(wj, lb, ob, s, d, v)`: one step of Knuth's algorithm D on the window of `lb + 1`
limbs at `wj` (con-ron's `dm_step` for `|b| ≥ 2`): the estimate from the window's top three limbs
read shifted by `s` against `d`, `b`'s top two limbs shifted by `s`; then `div_submul` and the
correction. Returns the quotient digit; the window is left holding the remainder. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divKstep : FunDecl := lfn (wj, lb, ob, s, d, v) locals (x, c, q, u1, u0, r) {
  x := POOL⦃wj + lb⦄;
  c := POOL⦃wj + lb - 1⦄;
  u1 := (x << s) + ((c >> 1) >> (63 - s));
  x := POOL⦃wj + lb - 2⦄;
  u0 := (c << s) + ((x >> 1) >> (63 - s));
  if d <= u1 { q := 0 - 1 } else { (q, r) := call div_2by1(u1, u0, d, v) };
  c := call div_submul(wj, lb, ob, q);
  ⟪dcLoop⟫;
  return q
}

/-- One-limb divisor: the limbs of `a` from the top, one `div_2by1` each, the remainder
(normalised, `r · 2^s`) in a word. -/
def d1Loop : Stmt := lblk (oa, la, ob, lb, top, n, w, i, j, x, c, q, r, s, d, v, pt, pb) {
  while 0 < i {
    i -= 1;
    x := POOL⦃oa + i⦄;
    (q, r) := call div_2by1(r + ((x >> 1) >> (63 - s)), x << s, d, v);
    POOL⟨pt⟩[pb + i] := q
  }
}

/-- The copy of `a` into the work region at `w`. -/
def dcpLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, i, j, x, c, q, r, s, d, v, pt, pb) {
  for i < la { POOL⟨pt⟩[pb + n + i] := POOL⦃oa + i⦄ }
}

/-- Knuth's algorithm D, one quotient limb `j` per step from the top (con-ron's `dm_limbs`). -/
def dkLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, i, j, x, c, q, r, s, d, v, pt, pb) {
  while 0 < j {
    j -= 1;
    q := call div_kstep(w + j, lb, ob, s, d, v);
    POOL⟨pt⟩[pb + j] := q
  }
}

/-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natDivmod : FunDecl := lfn (oa, la, ob, lb)
    locals (top, n, w, i, j, x, c, q, r, s, d, v, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if lb == 0 || la < lb {
    c := call nat_trim(oa, la);
    return (top, 0, oa, c)
  };
  if lb == 1 {
    if len(POOL⟨pt⟩) - pb <= la { abort };
    d := POOL⦃ob⦄;
    s := call div_norm(d);
    d := d << s;
    v := call div_recip(d);
    i := la;
    ⟪d1Loop⟫;
    POOL⟨pt⟩[pb + la] := r >> s;
    x := call nat_trim(top, la);
    c := call nat_trim(top + la, 1);
    CTL.u64[0] := top + la + 1;
    return (top, x, top + la, c)
  };
  n := la - lb + 1;
  if len(POOL⟨pt⟩) - pb < n { abort };
  if len(POOL⟨pt⟩) - pb - n <= la { abort };
  w := top + n;
  ⟪dcpLoop⟫;
  POOL⟨pt⟩[pb + n + la] := 0;
  d := POOL⦃ob + lb - 1⦄;
  s := call div_norm(d);
  x := POOL⦃ob + lb - 2⦄;
  d := (d << s) + ((x >> 1) >> (63 - s));
  v := call div_recip(d);
  j := n;
  ⟪dkLoop⟫;
  x := call nat_trim(top, n);
  c := call nat_trim(w, lb);
  CTL.u64[0] := w + lb;
  return (top, x, w, c)
}

/-- The pool functions with `nat_divmod`. -/
def natDivProg : Prog := natProg ++ [("div_add", divAdd), ("div_norm", divNorm),
  ("div_recip", divRecip), ("div_2by1", div2by1), ("div_submul", divSubmul),
  ("div_kstep", divKstep), ("nat_divmod", natDivmod)]

/- `(2^64 + 5) / 3 = 6148914691236517207, rem 0`; quotient `[0x5555555555555557]`. -/
#guard (run natDivProg 100000 "nat_divmod" [0, 2, 2, 1]
  (Mem.ofWords [(POOL, #[5, 1, 3, 0, 0, 0, 0, 0]), (CTL, #[3])])).toOption.map
  (fun (r, m) => (r, (m.arr64 POOL)[3]!, m.arr64 CTL)) ==
  some ([3, 1, 5, 0], 0x5555555555555557, #[6])
/- `7 / 2 = 3 rem 1`; `5 / 0 = 0 rem 5` (the remainder is `a`'s slice). -/
#guard (run natDivProg 100000 "nat_divmod" [0, 1, 1, 1]
  (Mem.ofWords [(POOL, #[7, 2, 0, 0, 0, 0]), (CTL, #[2])])).toOption.map
  (fun (r, m) => (r, (m.arr64 POOL)[2]!, (m.arr64 POOL)[3]!)) == some ([2, 1, 3, 1], 3, 1)
#guard (run natDivProg 100000 "nat_divmod" [0, 1, 1, 0]
  (Mem.ofWords [(POOL, #[5, 0]), (CTL, #[1])])).toOption.map (·.1) == some [1, 0, 0, 1]
/- `(2^128 - 1) / (2^64 + 1) = 2^64 - 1 rem 0`: the estimate is capped at `2^64 - 1`. -/
#guard (run natDivProg 100000 "nat_divmod" [0, 2, 2, 2]
  (Mem.ofWords [(POOL, #[0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 1, 1] ++ Array.replicate 8 0),
    (CTL, #[4])])).toOption.map
  (fun (r, m) => (r, (m.arr64 POOL)[4]!)) == some ([4, 1, 5, 0], 0xFFFFFFFFFFFFFFFF)

/-- The functions `nat_divmod` calls, transitively, as the program `p` binds them. -/
structure DivFns (p : Prog) : Prop where
  limb : p.lookup "nat_limb" = some natLimb
  carry : p.lookup "add_carry" = some addCarry
  add : p.lookup "div_add" = some divAdd
  norm : p.lookup "div_norm" = some divNorm
  d2by1 : p.lookup "div_2by1" = some div2by1
  recip : p.lookup "div_recip" = some divRecip
  submul : p.lookup "div_submul" = some divSubmul
  kstep : p.lookup "div_kstep" = some divKstep
  trim : p.lookup "nat_trim" = some natTrim
  divmod : p.lookup "nat_divmod" = some natDivmod

section specs
variable (p : Prog) (hf : DivFns p)

set_option maxHeartbeats 4000000 in
include hf in
/-- `nat_divmod` returns two normalised slices in use, `(oq, lq)` denoting `a / b` and
`(or, lr)` denoting `a % b`; the memory grew. `b` must be normalised (its length decides). -/
theorem natDivmod_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_divmod" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat / pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      SliceOK s'.mem (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat % pv (vpool s₀.mem) ob.toNat lb.toNat; ⊤⦄ := by
  sorry

end specs

end L.Arena
