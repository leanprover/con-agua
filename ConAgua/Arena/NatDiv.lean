module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatSub
meta import ConAgua.Arena.NatAdd
meta import ConAgua.Arena.NatDivWord
meta import ConAgua.Arena.NatDivKstep
import ConAgua.Census.Attr
public import ConAgua.Arena.NatDivKstep
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

/-- One-limb divisor: the limbs of `a` from the top, one `div_2by1` each, the remainder
(normalised, `r · 2^s`) in a word. -/
def d1Loop : Stmt := lblk (oa, la, ob, top, i, x, q, r, s, d, v, pt, pb) {
  while 0 < i {
    i -= 1;
    x := POOL⦃oa + i⦄;
    (q, r) := call div_2by1(r + ((x >> 1) >> (63 - s)), x << s, d, v);
    POOL⟨pt⟩[pb + i] := q
  }
}

/-- `div_mod1(oa, la, ob)`: `nat_divmod` for a one-limb divisor (con-ron's `u128` case of
`dm_step`): the quotient's `la` limbs at the top, then the remainder's one limb. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divMod1 : FunDecl := lfn (oa, la, ob) locals (top, i, x, q, r, s, d, v, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) - pb <= la { abort };
  d := POOL⦃ob⦄;
  s := call div_norm(d);
  d := d << s;
  v := call div_recip(d);
  i := la;
  ⟪d1Loop⟫;
  POOL⟨pt⟩[pb + la] := r >> s;
  x := call nat_trim(top, la);
  r := call nat_trim(top + la, 1);
  CTL.u64[0] := top + la + 1;
  return (top, x, top + la, r)
}

/-- The copy of `a` into the work region at `w`. -/
def dcpLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, i, j, x, q, s, d, v, pt, pb) {
  for i < la { POOL⟨pt⟩[pb + (n + i)] := POOL⦃oa + i⦄ }
}

/-- Knuth's algorithm D, one quotient limb `j` per step from the top (con-ron's `dm_limbs`). -/
def dkLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, i, j, x, q, s, d, v, pt, pb) {
  while 0 < j {
    j -= 1;
    q := call div_kstep(w + j, lb, ob, s, d, v);
    POOL⟨pt⟩[pb + j] := q
  }
}

/-- `div_modk(oa, la, ob, lb)`: `nat_divmod` for `2 ≤ lb ≤ la` (Knuth's algorithm D): the
`la - lb + 1` quotient limbs at the top, then the work region `w` (a copy of `a` and a zero limb),
whose low `lb` limbs end as the remainder. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `ron/nat.rs`); the twin computes on `Nat`
@[no_expose] def divModK : FunDecl := lfn (oa, la, ob, lb)
    locals (top, n, w, i, j, x, q, s, d, v, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := la - lb + 1;
  if len(POOL⟨pt⟩) - pb < n { abort };
  if len(POOL⟨pt⟩) - pb - n <= la { abort };
  w := top + n;
  d := POOL⦃ob + lb - 1⦄;
  s := call div_norm(d);
  x := POOL⦃ob + lb - 2⦄;
  d := (d << s) + ((x >> 1) >> (63 - s));
  v := call div_recip(d);
  ⟪dcpLoop⟫;
  POOL⟨pt⟩[pb + (n + la)] := 0;
  j := n;
  ⟪dkLoop⟫;
  x := call nat_trim(top, n);
  q := call nat_trim(w, lb);
  CTL.u64[0] := w + lb;
  return (top, x, w, q)
}

/-- con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natDivmod : FunDecl := lfn (oa, la, ob, lb) locals (top, x, o, c) {
  if lb == 0 || la < lb {
    top := CTL.u64[0];
    c := call nat_trim(oa, la);
    return (top, 0, oa, c)
  };
  if lb == 1 {
    (top, x, o, c) := call div_mod1(oa, la, ob);
    return (top, x, o, c)
  };
  (top, x, o, c) := call div_modk(oa, la, ob, lb);
  return (top, x, o, c)
}

/-- The pool functions with `nat_divmod`. -/
def natDivProg : Prog := natProg ++ [("div_add", divAdd), ("div_norm", divNorm),
  ("div_recip", divRecip), ("div_2by1", div2by1), ("div_submul", divSubmul),
  ("div_kstep", divKstep), ("div_mod1", divMod1), ("div_modk", divModK),
  ("nat_divmod", natDivmod)]

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

/-- The remainder of the one-limb loop plus the high bits of the next limb shifted by `s` stay
below the normalised divisor: both are multiples of `2^s`. -/
theorem d1_hi_lt (r x s d : Word) (hs : s.toNat ≤ 63) (hr : r.toNat < d.toNat)
    (hdr : sh s.toNat ∣ r.toNat) (hdd : sh s.toNat ∣ d.toNat) :
    r.toNat + ((x >>> 1) >>> (63 - s)).toNat < d.toNat := by
  have h2 := shl_hi_lt' x s (by omega)
  obtain ⟨a, ha⟩ := hdr
  obtain ⟨c, hc⟩ := hdd
  have hac : a < c := by
    rw [ha, hc] at hr; exact Nat.lt_of_mul_lt_mul_left hr
  have : r.toNat + sh s.toNat ≤ d.toNat := by
    rw [ha, hc]
    have : sh s.toNat * a + sh s.toNat = sh s.toNat * (a + 1) := by grind
    rw [this]; exact Nat.mul_le_mul_left _ hac
  omega

theorem d1_u1_lt (r x s d : Word) (hs : s.toNat ≤ 63) (hr : r.toNat < d.toNat)
    (hdr : sh s.toNat ∣ r.toNat) (hdd : sh s.toNat ∣ d.toNat) :
    (r + ((x >>> 1) >>> (63 - s))).toNat < d.toNat := by
  have h := d1_hi_lt r x s d hs hr hdr hdd
  have hd := d.toNat_lt
  rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega)]
  exact h

/-- What one `div_2by1` of the one-limb loop gives: the dividend is `r · 2^64 + x · 2^s`, and the
new remainder is again a multiple of `2^s`. -/
theorem d1_facts (q d r' r x s : Word)
    (h : q.toNat * d.toNat + r'.toNat =
        (r + ((x >>> 1) >>> (63 - s))).toNat * 2 ^ 64 + (x <<< s).toNat ∧ r'.toNat < d.toNat)
    (hs : s.toNat ≤ 63) (hr : r.toNat < d.toNat) (hdr : sh s.toNat ∣ r.toNat)
    (hdd : sh s.toNat ∣ d.toNat) :
    q.toNat * d.toNat + r'.toNat = r.toNat * 2 ^ 64 + x.toNat * sh s.toNat ∧
      sh s.toNat ∣ r'.toNat := by
  have hu := d1_u1_lt r x s d hs hr hdr hdd
  have hd := d.toNat_lt
  have h1 := shl_hi x s (by omega)
  have h0 := shl_lo x s (by omega)
  have hh := d1_hi_lt r x s d hs hr hdr hdd
  have e1 : (r + ((x >>> 1) >>> (63 - s))).toNat = r.toNat + x.toNat * sh s.toNat / 2 ^ 64 := by
    rw [UInt64.toNat_add, Nat.mod_eq_of_lt (by omega), h1]; rfl
  have hdm := Nat.div_add_mod (x.toNat * sh s.toNat) (2 ^ 64)
  have hU : q.toNat * d.toNat + r'.toNat = r.toNat * 2 ^ 64 + x.toNat * sh s.toNat := by
    rw [h.1, e1, h0]; simp only [sh] at *; grind
  refine ⟨hU, ?_⟩
  have hS : sh s.toNat ∣ 2 ^ 64 := ⟨2 ^ (64 - s.toNat), by simp only [sh, ← Nat.pow_add]; congr 1; omega⟩
  have h3 : sh s.toNat ∣ r.toNat * 2 ^ 64 + x.toNat * sh s.toNat :=
    Nat.dvd_add (Nat.dvd_mul_right_of_dvd hdr _) (Nat.dvd_mul_left _ _)
  have h4 : sh s.toNat ∣ q.toNat * d.toNat := Nat.dvd_mul_left_of_dvd hdd _
  rw [← hU] at h3
  exact (Nat.dvd_add_right h4).mp h3

/-- Writing a limb at the start of a slice and prepending it. -/
theorem pv_set_cons (p : Array Word) (o o' k k' j : Nat) (v : Word) (hj : j = o) (ho : o' = o + 1)
    (hk : k' = k + 1) (h : o < p.size) :
    pv (p.set! j v) o k' = v.toNat + 2 ^ 64 * pv p o' k :=
  pv_set_cons_off p p o o' k k' j (o + k') 0 v (Off.refl p (o + k') 0) hj ho hk (by omega) h
grind_pattern [natop_grind] pv_set_cons => pv (p.set! j v) o k', pv p o' k

/-- `div_2by1` as the one-limb loop calls it: the dividend `r · 2^64 + x · 2^s` (`r` a multiple
of `2^s` below `d`), and the new remainder again a multiple of `2^s`. -/
theorem div2by1_d1_spec (p : Prog) (hp2 : p.lookup "div_2by1" = some div2by1) (n : Nat) (s₀ : St)
    (r x s d v : Word) (hs : s.toNat ≤ 63) (hr : r.toNat < d.toNat)
    (hdr : sh s.toNat ∣ r.toNat) (hdd : sh s.toNat ∣ d.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_2by1" [BinOp.add.eval r (BinOp.shr.eval (BinOp.shr.eval x 1)
      (BinOp.sub.eval 63 s)), BinOp.shl.eval x s, d, v]
    ⦃fun res s' => s' = s₀ ∧
      (res.headD 0).toNat * d.toNat + (res.tail.headD 0).toNat =
        r.toNat * 2 ^ 64 + x.toNat * sh s.toNat ∧
      sh s.toNat ∣ (res.tail.headD 0).toNat ∧ (res.tail.headD 0).toNat < d.toNat; ⊤⦄ := by
  apply M.triple_of_run
  intro s' res s'' hs' hrun
  obtain ⟨h1, h2, h3⟩ := M.of_run (P := fun s => s = s₀) hs' hrun
    (div2by1_spec p hp2 n s₀ _ (x <<< s) d v (d1_u1_lt r x s d hs hr hdr hdd))
  have := d1_facts _ _ _ _ _ _ ⟨h2, h3⟩ hs hr hdr hdd
  exact ⟨h1, this.1, this.2, h3⟩

/-! ## `Same`: a copied window -/

/-- The `n` words of `p` at `o` are those of `q` at `o'`. -/
def Same (p q : Array Word) (o o' n : Nat) : Prop := ∀ k, k < n → p[o + k]? = q[o' + k]?

theorem Same.zero (p q : Array Word) (o o' : Nat) : Same p q o o' 0 := fun _ h => absurd h (by omega)

theorem Same.pv {p q : Array Word} {o o' n : Nat} (h : Same p q o o' n) (k : Nat) (hk : k ≤ n) :
    pv p o k = pv q o' k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [L.Arena.pv, ih (by omega), h k (by omega)]

theorem Same.get {p q : Array Word} {o o' n : Nat} (h : Same p q o o' n) (k : Nat) (hk : k < n)
    (hp : o + k < p.size) (hq : o' + k < q.size) : p[o + k] = q[o' + k] := by
  have := h k hk; simp [hp, hq] at this; exact this

theorem Same.set_succ {p q : Array Word} {o o' n : Nat} (h : Same p q o o' n) (j : Nat) (v : Word)
    (hj : j = o + n) (hv : q[o' + n]? = some v) (hs : j < p.size) :
    Same (p.set! j v) q o o' (n + 1) := by
  intro k hk
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases e : j = o + k
  · simp only [e, ite_true, show o + k < p.size by omega]
    have : k = n := by omega
    subst this; exact hv.symm
  · simp only [e, ite_false]; exact h k (by omega)

theorem Same.set_above {p q : Array Word} {o o' n : Nat} (h : Same p q o o' n) (j : Nat) (v : Word)
    (hj : o + n ≤ j) : Same (p.set! j v) q o o' n := by
  intro k hk
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp only [show j ≠ o + k by omega, ite_false]; exact h k hk

theorem Same.set_below {p q : Array Word} {o o' n : Nat} (h : Same p q o o' n) (j : Nat) (v : Word)
    (hj : j < o) : Same (p.set! j v) q o o' n := by
  intro k hk
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp only [show j ≠ o + k by omega, ite_false]; exact h k hk

theorem Same.off {p p' q : Array Word} {o o' n r m : Nat} (h : Same p q o o' n) (ho : Off p' p r m)
    (hr : o + n ≤ r) : Same p' q o o' n := fun k hk => (ho (o + k) (Or.inl (by omega))).trans (h k hk)

theorem Same.mono {p q : Array Word} {o o' n n' : Nat} (h : Same p q o o' n) (hn : n' ≤ n) :
    Same p q o o' n' := fun k hk => h k (by omega)

section d1
variable (p : Prog) (hp2 : p.lookup "div_2by1" = some div2by1) (Pg : Array Word) (C b0 : Nat)

/-- The one-limb loop: the top `la - i` limbs of `a`, scaled by `2^s`, are the quotient limbs
written so far times `d = b0 · 2^s` plus the remainder `r` (a multiple of `2^s`, below `d`). -/
def D1Inv (Pg : Array Word) (C b0 : Nat) (s : St) : Prop :=
  C < 2 ^ 63 ∧ Pg.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  Agree (vpool s.mem) Pg (s.loc 3).toNat ∧
  s.loc 11 = s.loc 3 >>> 40 ∧ s.loc 12 = s.loc 3 &&& 1099511627775 ∧
  (s.loc 12).toNat + (s.loc 1).toNat + 1 ≤ (s.mem.arr64 (tierA POOL (s.loc 11))).size ∧
  (s.mem.arr64 (tierA POOL (s.loc 11))).size ≤ 2 ^ 40 ∧ (s.loc 11).toNat ≤ 1 ∧
  (s.loc 3).toNat < 2 ^ 41 ∧ (s.loc 3).toNat + (s.loc 1).toNat + 1 ≤ C ∧
  (s.loc 3).toNat + (s.loc 1).toNat + 1 ≤ 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 3).toNat ∧
  (s.loc 8).toNat ≤ 63 ∧ (s.loc 9).toNat = b0 * sh (s.loc 8).toNat ∧
  sh (s.loc 8).toNat ∣ (s.loc 9).toNat ∧
  (s.loc 4).toNat ≤ (s.loc 1).toNat ∧ (s.loc 7).toNat < (s.loc 9).toNat ∧
  sh (s.loc 8).toNat ∣ (s.loc 7).toNat ∧
  pv Pg ((s.loc 0).toNat + (s.loc 4).toNat) ((s.loc 1).toNat - (s.loc 4).toNat) *
      sh (s.loc 8).toNat =
    pv (vpool s.mem) ((s.loc 3).toNat + (s.loc 4).toNat) ((s.loc 1).toNat - (s.loc 4).toNat) *
      (s.loc 9).toNat + (s.loc 7).toNat

def D1Post (Pg : Array Word) (C b0 : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ pcap s'.mem = C ∧
  Agree (vpool s'.mem) Pg (s₀.loc 3).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 8 = s₀.loc 8 ∧ s'.loc 9 = s₀.loc 9 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧
  (s₀.loc 3).toNat < 2 ^ 41 ∧ (s'.mem.arr64 (tierA POOL (s₀.loc 11))).size ≤ 2 ^ 40 ∧
  (s₀.loc 12).toNat + (s₀.loc 1).toNat + 1 ≤ (s'.mem.arr64 (tierA POOL (s₀.loc 11))).size ∧
  (s₀.loc 8).toNat ≤ 63 ∧ (s₀.loc 9).toNat = b0 * sh (s₀.loc 8).toNat ∧
  (s'.loc 7).toNat < (s₀.loc 9).toNat ∧ sh (s₀.loc 8).toNat ∣ (s'.loc 7).toNat ∧
  pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * sh (s₀.loc 8).toNat =
    pv (vpool s'.mem) (s₀.loc 3).toNat (s₀.loc 1).toNat * (s₀.loc 9).toNat + (s'.loc 7).toNat

/-- One step of the one-limb loop, in the shape of its verification condition: `s` the state
before the step (the invariant `h`), `rs` what `div_2by1` returned. -/
theorem d1_step_goal (Pg : Array Word) (C b0 : Nat) (s : St) (rs : List Word)
    (h : D1Inv Pg C b0 s) (hi : 0 < s.loc 4)
    (hlx : ((s.loc 0 + (s.loc 4 - 1)) &&& 1099511627775).toNat <
      (s.mem.arr64 (tierA POOL ((s.loc 0 + (s.loc 4 - 1)) >>> 40))).size)
    (h2 : (rs.headD 0).toNat * (s.loc 9).toNat + (rs.tail.headD 0).toNat =
      (s.loc 7).toNat * 2 ^ 64 +
        (s.mem.arr64 (tierA POOL ((s.loc 0 + (s.loc 4 - 1)) >>> 40)))[((s.loc 0 + (s.loc 4 - 1)) &&&
          1099511627775).toNat].toNat * sh (s.loc 8).toNat) :
    pv Pg ((s.loc 0).toNat + (s.loc 4 - 1).toNat) ((s.loc 1).toNat - (s.loc 4 - 1).toNat) *
        sh (s.loc 8).toNat =
      pv (vpool (s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + (s.loc 4 - 1)) (rs.headD 0)))
          ((s.loc 3).toNat + (s.loc 4 - 1).toNat) ((s.loc 1).toNat - (s.loc 4 - 1).toNat) *
        (s.loc 9).toNat + (rs.tail.headD 0).toNat := by
  obtain ⟨_, hPg, _, hag, h11, h12, hroom, hsz, _, hT, _, h41, hoa, _, _, _, hil, _, _, ih⟩ := h
  have hroom' := hroom
  rw [h12, tag_idx_toNat] at hroom'
  have hvs := vpool_size s.mem
  have hi0 : 0 < (s.loc 4).toNat := hi
  have hi1' : (1 : Word) ≤ s.loc 4 := by
    rw [UInt64.le_iff_toNat_le, UInt64.toNat_one]; omega
  have hi1 : (s.loc 4 - 1).toNat = (s.loc 4).toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ hi1', UInt64.toNat_one]
  have hlt : (s.loc 0).toNat + ((s.loc 4).toNat - 1) < (s.loc 3).toNat := by omega
  have hoi : (s.loc 0 + (s.loc 4 - 1)).toNat = (s.loc 0).toNat + ((s.loc 4).toNat - 1) := by
    rw [UInt64.toNat_add, hi1]; exact Nat.mod_eq_of_lt (by omega)
  have ex : (s.mem.arr64 (tierA POOL ((s.loc 0 + (s.loc 4 - 1)) >>> 40)))[((s.loc 0 +
      (s.loc 4 - 1)) &&& 1099511627775).toNat] = Pg[(s.loc 0).toNat + ((s.loc 4).toNat - 1)] := by
    rw [vpool_ld s.mem _ hlx (by rw [hoi, hvs]; omega)]
    simp only [hoi]
    exact Agree.get _ _ _ _ hag hlt (by omega) (by omega)
  rw [ex] at h2
  rw [h11, h12, vpool_stidx s.mem (s.loc 3) (s.loc 4 - 1) _ hT (by rw [← h11, ← h12]; grind) (by grind)
    (by rw [tag_idx_toNat]; omega)]
  have hti : (s.loc 3 + (s.loc 4 - 1)).toNat = (s.loc 3).toNat + ((s.loc 4).toNat - 1) := by
    rw [UInt64.toNat_add, hi1]; exact Nat.mod_eq_of_lt (by omega)
  rw [hti, hi1,
    pv_set_cons (vpool s.mem) _ ((s.loc 3).toNat + (s.loc 4).toNat)
      ((s.loc 1).toNat - (s.loc 4).toNat) _ _ _ rfl (by omega) (by omega) (by omega),
    pv_cons Pg _ ((s.loc 0).toNat + (s.loc 4).toNat) ((s.loc 1).toNat - (s.loc 4).toNat) _
      (by omega) (by omega) (by omega)]
  generalize pv Pg ((s.loc 0).toNat + (s.loc 4).toNat) ((s.loc 1).toNat - (s.loc 4).toNat) = A at *
  generalize pv (vpool s.mem) ((s.loc 3).toNat + (s.loc 4).toNat)
    ((s.loc 1).toNat - (s.loc 4).toNat) = Q at *
  generalize Pg[(s.loc 0).toNat + ((s.loc 4).toNat - 1)].toNat = X at *
  generalize (rs.headD 0).toNat = q at *
  generalize (rs.tail.headD 0).toNat = r' at *
  generalize sh (s.loc 8).toNat = S at *
  generalize (s.loc 9).toNat = D at *
  generalize (s.loc 7).toNat = R at *
  grind

include hp2 in
theorem d1Loop_spec (n : Nat) (s₀ : St) (h : D1Inv Pg C b0 s₀) :
    ⦃fun s => s = s₀⦄ exec p n d1Loop ⦃fun r s' => D1Post Pg C b0 s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    have h' := h
    simp only [D1Inv] at h'
    simp only [D1Post]
    rw [exec, step_while (w := d1Loop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih, div2by1_d1_spec p hp2 n]
    all_goals clear ih
    all_goals (try simp only [D1Post] at *)
    all_goals (try simp only [D1Inv] at ⊢)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil,
      Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 20) [arena_grind, lang_grind]; done)
      | (apply d1_step_goal Pg C b0 _ _ h <;> grind)

include hp2 in
theorem d1Loop_step_spec (n : Nat) (s₀ : St) (h : D1Inv Pg C b0 s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) d1Loop ⦃fun r s' => D1Post Pg C b0 s₀ r s'; ⊤⦄ :=
  Triple.step_exec (d1Loop_spec p hp2 Pg C b0 (n + 1) s₀ h)

end d1

section dk
variable (p : Prog) (Pg : Array Word) (C : Nat)

/-- What the loops of `div_modk` keep: the pool agrees with the entry pool below `top`; the
`n = la - lb + 1` quotient limbs at `top` and the work region `w = top + n` of `la + 1` limbs
fit in `top`'s tier; `a` and `b` lie below `top`. -/
def KBase (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  C < 2 ^ 63 ∧ Pg.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  s.loc 14 = s.loc 4 >>> 40 ∧ s.loc 15 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 15).toNat + (s.loc 5).toNat + (s.loc 1).toNat + 1 ≤
    (s.mem.arr64 (tierA POOL (s.loc 14))).size ∧
  (s.mem.arr64 (tierA POOL (s.loc 14))).size ≤ 2 ^ 40 ∧ (s.loc 14).toNat ≤ 1 ∧
  (s.loc 4).toNat < 2 ^ 41 ∧ (s.loc 4).toNat + (s.loc 5).toNat + (s.loc 1).toNat + 1 ≤ 2 ^ 41 ∧
  (s.loc 4).toNat + (s.loc 5).toNat + (s.loc 1).toNat + 1 ≤ C ∧
  (s.loc 6).toNat = (s.loc 4).toNat + (s.loc 5).toNat ∧
  (s.loc 5).toNat + (s.loc 3).toNat = (s.loc 1).toNat + 1 ∧ 2 ≤ (s.loc 3).toNat ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧
  (s.loc 2).toNat + (s.loc 3).toNat ≤ (s.loc 4).toNat

/-- The copy loop: the first `i` limbs of the work region are `a`'s. -/
def DcpInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  KBase Pg C s ∧ (s.loc 7).toNat ≤ (s.loc 1).toNat ∧
  Same (vpool s.mem) Pg (s.loc 6).toNat (s.loc 0).toNat (s.loc 7).toNat

def DcpPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ KBase Pg C s' ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
  s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 13 = s₀.loc 13 ∧
  s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧
  Same (vpool s'.mem) Pg (s₀.loc 6).toNat (s₀.loc 0).toNat (s₀.loc 1).toNat

/-- One step of the copy loop, in the shape of its verification condition. -/
theorem dcp_step_goal (Pg : Array Word) (C : Nat) (s : St) (h : DcpInv Pg C s)
    (hi : s.loc 7 < s.loc 1)
    (hlx : ((s.loc 0 + s.loc 7) &&& 1099511627775).toNat <
      (s.mem.arr64 (tierA POOL ((s.loc 0 + s.loc 7) >>> 40))).size) :
    Same (vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 7))
        (s.mem.arr64 (tierA POOL ((s.loc 0 + s.loc 7) >>> 40)))[((s.loc 0 + s.loc 7) &&&
          1099511627775).toNat]))
      Pg (s.loc 6).toNat (s.loc 0).toNat (s.loc 7 + 1).toNat := by
  obtain ⟨⟨_, hPg, _, hag, h14, h15, hroom, hsz, _, hT, h41, _, h6, _, _, hoa, _⟩, _, hsame⟩ := h
  have hi' : (s.loc 7).toNat < (s.loc 1).toNat := hi
  have hvs := vpool_size s.mem
  have hroom' := hroom
  rw [h15, tag_idx_toNat] at hroom'
  have e1 : (s.loc 7 + 1).toNat = (s.loc 7).toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; omega
  have e2 : (s.loc 0 + s.loc 7).toNat = (s.loc 0).toNat + (s.loc 7).toNat := by
    rw [UInt64.toNat_add]; omega
  have e3 : (s.loc 5 + s.loc 7).toNat = (s.loc 5).toNat + (s.loc 7).toNat := by
    rw [UInt64.toNat_add]; omega
  have e4 : (s.loc 4 + (s.loc 5 + s.loc 7)).toNat = (s.loc 6).toNat + (s.loc 7).toNat := by
    rw [UInt64.toNat_add, e3]; omega
  have ex : (s.mem.arr64 (tierA POOL ((s.loc 0 + s.loc 7) >>> 40)))[((s.loc 0 + s.loc 7) &&&
      1099511627775).toNat] = Pg[(s.loc 0).toNat + (s.loc 7).toNat] := by
    rw [vpool_ld s.mem _ hlx (by rw [e2, hvs]; omega)]
    simp only [e2]
    exact Agree.get _ _ _ _ hag (by omega) (by omega) (by omega)
  rw [ex, h14, h15, vpool_stidx s.mem (s.loc 4) (s.loc 5 + s.loc 7) _ hT
    (by rw [← h14, ← h15, UInt64.toNat_add, h15, e3]; rw [tag_idx_toNat]; omega) (by rw [← h14]; exact hsz)
    (by rw [tag_idx_toNat, e3]; omega), e4, e1]
  exact hsame.set_succ _ _ rfl (by simp [Array.getElem?_eq_getElem (by omega : (s.loc 0).toNat + (s.loc 7).toNat < Pg.size)])
    (by rw [hvs]; omega)

theorem dcpLoop_spec (n : Nat) (s₀ : St) (h : DcpInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n dcpLoop ⦃fun r s' => DcpPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    have h' := h
    simp only [DcpInv, KBase] at h'
    simp only [DcpPost]
    rw [exec, step_while (w := dcpLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [DcpPost, KBase] at *)
    all_goals (try simp only [DcpInv, KBase] at ⊢)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, Cmp.eval, BinOp.eval,
      Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 20) [arena_grind, lang_grind]; done)
      | (apply dcp_step_goal Pg C _ h <;> grind)

theorem dcpLoop_step_spec (n : Nat) (s₀ : St) (h : DcpInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) dcpLoop ⦃fun r s' => DcpPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (dcpLoop_spec p Pg C (n + 1) s₀ h)

/-- Knuth's loop before step `j` (from the top): the low `j` limbs of the work region are still
`a`'s; above them `R` (the `lb` limbs at `w + j`, below `b`) is the remainder of the top limbs of
`a` by `b`, and the quotient limbs written so far are at `top + j`. -/
def DkInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  KBase Pg C s ∧ (s.loc 8).toNat ≤ (s.loc 5).toNat ∧ (s.loc 11).toNat ≤ 63 ∧
  (s.loc 12).toNat = pv Pg (s.loc 2).toNat (s.loc 3).toNat * sh (s.loc 11).toNat /
    wt ((s.loc 3).toNat - 1) ∧ 0 < (s.loc 12).toNat ∧
  Same (vpool s.mem) Pg (s.loc 6).toNat (s.loc 0).toNat (s.loc 8).toNat ∧
  pv (vpool s.mem) ((s.loc 6).toNat + (s.loc 8).toNat) (s.loc 3).toNat <
    pv Pg (s.loc 2).toNat (s.loc 3).toNat ∧
  pv Pg (s.loc 0).toNat (s.loc 1).toNat =
    pv Pg (s.loc 0).toNat (s.loc 8).toNat + wt (s.loc 8).toNat *
      (pv (vpool s.mem) ((s.loc 4).toNat + (s.loc 8).toNat) ((s.loc 5).toNat - (s.loc 8).toNat) *
        pv Pg (s.loc 2).toNat (s.loc 3).toNat +
       pv (vpool s.mem) ((s.loc 6).toNat + (s.loc 8).toNat) (s.loc 3).toNat)

def DkPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧ KBase Pg C s' ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 6 = s₀.loc 6 ∧
  s'.loc 14 = s₀.loc 14 ∧ s'.loc 15 = s₀.loc 15 ∧
  pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 3).toNat < pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat ∧
  pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat =
    pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 5).toNat * pv Pg (s₀.loc 2).toNat (s₀.loc 3).toNat +
      pv (vpool s'.mem) (s₀.loc 6).toNat (s₀.loc 3).toNat

/-- A slice whose value is below the weight of its top limb has a zero top limb. -/
theorem pv_drop_top (p : Array Word) (o k : Nat) (h : pv p o (k + 1) < wt k) :
    pv p o k = pv p o (k + 1) := by
  simp only [pv] at h ⊢
  have : (p[o + k]?.getD 0).toNat = 0 := by
    rcases Nat.eq_zero_or_pos (p[o + k]?.getD 0).toNat with h0 | h0
    · exact h0
    · exfalso
      have : wt k ≤ (p[o + k]?.getD 0).toNat * wt k := Nat.le_mul_of_pos_left _ h0
      omega
  rw [this]; simp

/-- What `div_kstep` leaves, relative to the state `s` before step `j` of Knuth's loop: `sk` is
the state after the call (`j` decremented), `rs` its result. -/
def DkStep (s sk : St) (rs : List Word) : Prop :=
  sk.loc 0 = s.loc 0 ∧ sk.loc 1 = s.loc 1 ∧ sk.loc 2 = s.loc 2 ∧ sk.loc 3 = s.loc 3 ∧
  sk.loc 4 = s.loc 4 ∧ sk.loc 5 = s.loc 5 ∧ sk.loc 6 = s.loc 6 ∧ sk.loc 8 = s.loc 8 - 1 ∧
  sk.loc 14 = s.loc 14 ∧ sk.loc 15 = s.loc 15 ∧ PFrame s.mem sk.mem ∧
  Off (vpool sk.mem) (vpool s.mem) (s.loc 6 + (s.loc 8 - 1)).toNat ((s.loc 3).toNat + 1) ∧
  (rs.headD 0).toNat = pv (vpool s.mem) (s.loc 6 + (s.loc 8 - 1)).toNat ((s.loc 3).toNat + 1) /
    pv (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat ∧
  pv (vpool sk.mem) (s.loc 6 + (s.loc 8 - 1)).toNat ((s.loc 3).toNat + 1) =
    pv (vpool s.mem) (s.loc 6 + (s.loc 8 - 1)).toNat ((s.loc 3).toNat + 1) %
      pv (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat

/-- The window of step `j` is below `b · 2^64` (`div_kstep`'s precondition). -/
theorem dk_pre_goal (Pg : Array Word) (C : Nat) (s : St) (h : DkInv Pg C s) (hj : 0 < s.loc 8) :
    pv (vpool s.mem) (s.loc 6 + (s.loc 8 - 1)).toNat ((s.loc 3).toNat + 1) <
      pv (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat * 2 ^ 64 := by
  obtain ⟨⟨_, hPg, _, hag, _, _, _, _, _, hT, h41, _, h6, hn, hlb, hoa, hob⟩, hjn, _, _, _, _, hR, _⟩ := h
  have hj0 : 0 < (s.loc 8).toNat := hj
  have hvs := vpool_size s.mem
  have e : (s.loc 6 + (s.loc 8 - 1)).toNat = (s.loc 6).toNat + ((s.loc 8).toNat - 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
      UInt64.toNat_one]; omega
  rw [e, pv_cons (vpool s.mem) _ ((s.loc 6).toNat + (s.loc 8).toNat) _ _ (by omega) rfl (by omega),
    Agree.pv _ _ _ (s.loc 2).toNat (s.loc 3).toNat hag hob]
  have := (vpool s.mem)[(s.loc 6).toNat + ((s.loc 8).toNat - 1)].toNat_lt
  generalize pv (vpool s.mem) ((s.loc 6).toNat + (s.loc 8).toNat) (s.loc 3).toNat = R at *
  generalize pv Pg (s.loc 2).toNat (s.loc 3).toNat = b at *
  have : (R + 1) * 2 ^ 64 ≤ b * 2 ^ 64 := Nat.mul_le_mul_right _ hR
  grind

/-- The quotient limb's store after `div_kstep`, as a store into the virtual pool at `top + j`. -/
theorem dk_store (Pg : Array Word) (C : Nat) (s sk : St) (rs : List Word) (v : Word)
    (h : DkInv Pg C s) (hj : 0 < s.loc 8) (hst : DkStep s sk rs) :
    vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) v) =
      (vpool sk.mem).set! ((s.loc 4).toNat + ((s.loc 8).toNat - 1)) v := by
  obtain ⟨⟨_, _, _, _, h14, h15, hroom, hsz, _, hT, h41, _, h6, hn, hlb, _, _⟩, hjn, _⟩ := h
  obtain ⟨_, _, _, _, _, _, _, hk8, hk14, hk15, hfr, _⟩ := hst
  have hj0 : 0 < (s.loc 8).toNat := hj
  have e8 : (sk.loc 8).toNat = (s.loc 8).toNat - 1 := by
    rw [hk8, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
      UInt64.toNat_one]
  have hroom' := hroom
  rw [h15, tag_idx_toNat] at hroom'
  have hsz' := hfr.tsize (s.loc 4 >>> 40)
  rw [h14] at hsz hroom'
  rw [hk14, hk15, h14, h15, vpool_stidx sk.mem (s.loc 4) (sk.loc 8) v hT
    (by rw [hsz', UInt64.toNat_add, e8, tag_idx_toNat]; omega)
    (by rw [hsz']; exact hsz) (by rw [tag_idx_toNat, e8]; omega)]
  congr 1
  rw [UInt64.toNat_add, e8]; omega

/-- After step `j`, the low `j - 1` limbs of the work region are still `a`'s. -/
theorem dk_same_goal (Pg : Array Word) (C : Nat) (s sk : St) (rs : List Word)
    (h : DkInv Pg C s) (hj : 0 < s.loc 8) (hst : DkStep s sk rs) :
    Same (vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) (rs.headD 0))) Pg
      (sk.loc 6).toNat (sk.loc 0).toNat (sk.loc 8).toNat := by
  rw [dk_store Pg C s sk rs _ h hj hst]
  obtain ⟨⟨_, _, _, _, _, _, _, _, _, hT, h41, _, h6, hn, hlb, _, _⟩, hjn, _, _, _, hsame, _⟩ := h
  obtain ⟨hk0, _, _, _, _, _, hk6, hk8, _, _, _, hoff, _⟩ := hst
  have hj0 : 0 < (s.loc 8).toNat := hj
  have e8 : (sk.loc 8).toNat = (s.loc 8).toNat - 1 := by
    rw [hk8, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
      UInt64.toNat_one]
  have e : (s.loc 6 + (s.loc 8 - 1)).toNat = (s.loc 6).toNat + ((s.loc 8).toNat - 1) := by
    rw [UInt64.toNat_add, ← hk8, e8]; omega
  rw [hk0, hk6, e8]
  rw [e] at hoff
  exact ((hsame.mono (by omega)).off hoff (by omega)).set_below _ _ (by omega)

/-- The window of step `j`: `T = a[j - 1] + 2^64 R`. -/
theorem dk_T (Pg : Array Word) (C : Nat) (s : St) (h : DkInv Pg C s) (hj : 0 < s.loc 8) :
    pv (vpool s.mem) ((s.loc 6).toNat + ((s.loc 8).toNat - 1)) ((s.loc 3).toNat + 1) =
      (Pg[(s.loc 0).toNat + ((s.loc 8).toNat - 1)]?.getD 0).toNat +
        2 ^ 64 * pv (vpool s.mem) ((s.loc 6).toNat + (s.loc 8).toNat) (s.loc 3).toNat := by
  obtain ⟨⟨_, hPg, _, _, _, _, _, _, _, hT, h41, _, h6, hn, hlb, hoa, _⟩, hjn, _, _, _, hsame,
    _, _⟩ := h
  have hj0 : 0 < (s.loc 8).toNat := hj
  have hvs := vpool_size s.mem
  rw [pv_cons (vpool s.mem) _ ((s.loc 6).toNat + (s.loc 8).toNat) _ _ (by omega) rfl (by omega)]
  have := hsame ((s.loc 8).toNat - 1) (by omega)
  rw [Array.getElem?_eq_getElem (by omega : (s.loc 6).toNat + ((s.loc 8).toNat - 1) < (vpool s.mem).size)] at this
  rw [← this]; rfl

/-- After step `j`, the new remainder `R'` (the window's low `lb` limbs), the quotient digit and
the quotient limbs `Q' = q + 2^64 Q`. -/
theorem dk_vals (Pg : Array Word) (C : Nat) (s sk : St) (rs : List Word)
    (h : DkInv Pg C s) (hj : 0 < s.loc 8) (hst : DkStep s sk rs) :
    pv (vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) (rs.headD 0)))
        ((sk.loc 6).toNat + (sk.loc 8).toNat) (sk.loc 3).toNat =
      pv (vpool s.mem) ((s.loc 6).toNat + ((s.loc 8).toNat - 1)) ((s.loc 3).toNat + 1) %
        pv Pg (s.loc 2).toNat (s.loc 3).toNat ∧
    (rs.headD 0).toNat =
      pv (vpool s.mem) ((s.loc 6).toNat + ((s.loc 8).toNat - 1)) ((s.loc 3).toNat + 1) /
        pv Pg (s.loc 2).toNat (s.loc 3).toNat ∧
    pv (vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) (rs.headD 0)))
        ((sk.loc 4).toNat + (sk.loc 8).toNat) ((sk.loc 5).toNat - (sk.loc 8).toNat) =
      (rs.headD 0).toNat +
        2 ^ 64 * pv (vpool s.mem) ((s.loc 4).toNat + (s.loc 8).toNat)
          ((s.loc 5).toNat - (s.loc 8).toNat) := by
  rw [dk_store Pg C s sk rs _ h hj hst]
  obtain ⟨⟨_, hPg, _, hag, _, _, _, _, _, hT, h41, _, h6, hn, hlb, hoa, hob⟩, hjn, _, _, _, _,
    hR, _⟩ := h
  obtain ⟨_, _, _, hk3, hk4, hk5, hk6, hk8, _, _, _, hoff, hq, hrem⟩ := hst
  have hj0 : 0 < (s.loc 8).toNat := hj
  have hvs := vpool_size s.mem
  have hvs' := vpool_size sk.mem
  have e8 : (sk.loc 8).toNat = (s.loc 8).toNat - 1 := by
    rw [hk8, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
      UInt64.toNat_one]
  have e : (s.loc 6 + (s.loc 8 - 1)).toNat = (s.loc 6).toNat + ((s.loc 8).toNat - 1) := by
    rw [UInt64.toNat_add, ← hk8, e8]; omega
  rw [e] at hoff hq hrem
  have hb : pv (vpool s.mem) (s.loc 2).toNat (s.loc 3).toNat = pv Pg (s.loc 2).toNat (s.loc 3).toNat :=
    Agree.pv _ _ _ _ _ hag hob
  rw [hb] at hq hrem
  have hbpos : 0 < pv Pg (s.loc 2).toNat (s.loc 3).toNat := by omega
  simp only [hk3, hk4, hk5, hk6, e8]
  refine ⟨?_, hq, ?_⟩
  · rw [pv_set_below _ _ _ _ _ (by omega), pv_drop_top _ _ _ ?_, hrem]
    have := Nat.mod_lt (pv (vpool s.mem) ((s.loc 6).toNat + ((s.loc 8).toNat - 1))
      ((s.loc 3).toNat + 1)) hbpos
    have := pv_lt_wt Pg (s.loc 2).toNat (s.loc 3).toNat
    rw [hrem]; omega
  · rw [show (s.loc 5).toNat - ((s.loc 8).toNat - 1) = (s.loc 5).toNat - (s.loc 8).toNat + 1 by omega,
      pv_set_cons _ _ ((s.loc 4).toNat + (s.loc 8).toNat) _ _ _ _ rfl (by omega) rfl (by omega)]
    rw [Off.pv_below _ _ _ _ _ _ hoff (by omega)]

theorem dk_rem_goal (Pg : Array Word) (C : Nat) (s sk : St) (rs : List Word)
    (h : DkInv Pg C s) (hj : 0 < s.loc 8) (hst : DkStep s sk rs) :
    pv (vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) (rs.headD 0)))
        ((sk.loc 6).toNat + (sk.loc 8).toNat) (sk.loc 3).toNat <
      pv Pg (sk.loc 2).toNat (sk.loc 3).toNat := by
  rw [(dk_vals Pg C s sk rs h hj hst).1, hst.2.2.1, hst.2.2.2.1]
  apply Nat.mod_lt
  obtain ⟨_, _, _, _, _, _, hR, _⟩ := h
  omega

theorem dk_eq_goal (Pg : Array Word) (C : Nat) (s sk : St) (rs : List Word)
    (h : DkInv Pg C s) (hj : 0 < s.loc 8) (hst : DkStep s sk rs) :
    pv Pg (sk.loc 0).toNat (sk.loc 1).toNat =
      pv Pg (sk.loc 0).toNat (sk.loc 8).toNat + wt (sk.loc 8).toNat *
        (pv (vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) (rs.headD 0)))
            ((sk.loc 4).toNat + (sk.loc 8).toNat) ((sk.loc 5).toNat - (sk.loc 8).toNat) *
          pv Pg (sk.loc 2).toNat (sk.loc 3).toNat +
         pv (vpool (sk.mem.set64 (tierA POOL (sk.loc 14)) (sk.loc 15 + sk.loc 8) (rs.headD 0)))
            ((sk.loc 6).toNat + (sk.loc 8).toNat) (sk.loc 3).toNat) := by
  obtain ⟨v1, v2, v3⟩ := dk_vals Pg C s sk rs h hj hst
  have hT := dk_T Pg C s h hj
  rw [v1, v3]
  have hj0 : 0 < (s.loc 8).toNat := hj
  obtain ⟨hk0, hk1, hk2, hk3, _, _, _, hk8, _⟩ := hst
  have e8 : (sk.loc 8).toNat = (s.loc 8).toNat - 1 := by
    rw [hk8, UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega),
      UInt64.toNat_one]
  obtain ⟨_, _, _, _, _, _, _, heq⟩ := h
  simp only [hk0, hk1, hk2, hk3, e8]
  have hpj : pv Pg (s.loc 0).toNat (s.loc 8).toNat = pv Pg (s.loc 0).toNat ((s.loc 8).toNat - 1) +
      (Pg[(s.loc 0).toNat + ((s.loc 8).toNat - 1)]?.getD 0).toNat * wt ((s.loc 8).toNat - 1) := by
    have : (s.loc 8).toNat = (s.loc 8).toNat - 1 + 1 := by omega
    conv => lhs; rw [this]
    rfl
  have hw := wt_succ ((s.loc 8).toNat - 1) (s.loc 8).toNat (by omega)
  rw [heq, hpj, hw]
  rw [v2] at *
  have hdm := Nat.div_add_mod
    (pv (vpool s.mem) ((s.loc 6).toNat + ((s.loc 8).toNat - 1)) ((s.loc 3).toNat + 1))
    (pv Pg (s.loc 2).toNat (s.loc 3).toNat)
  rw [hT] at hdm ⊢
  generalize pv (vpool s.mem) ((s.loc 6).toNat + (s.loc 8).toNat) (s.loc 3).toNat = R at *
  generalize pv Pg (s.loc 2).toNat (s.loc 3).toNat = b at *
  generalize (Pg[(s.loc 0).toNat + ((s.loc 8).toNat - 1)]?.getD 0).toNat = X at *
  generalize pv (vpool s.mem) ((s.loc 4).toNat + (s.loc 8).toNat) ((s.loc 5).toNat - (s.loc 8).toNat) = Q at *
  generalize (X + 2 ^ 64 * R) / b = q at *
  generalize (X + 2 ^ 64 * R) % b = r at *
  generalize wt ((s.loc 8).toNat - 1) = W at *
  generalize pv Pg (s.loc 0).toNat ((s.loc 8).toNat - 1) = A at *
  grind

set_option maxHeartbeats 4000000 in
theorem dkLoop_spec (hpl : p.lookup "nat_limb" = some natLimb)
    (hpc : p.lookup "add_carry" = some addCarry) (hpa : p.lookup "div_add" = some divAdd)
    (hp2 : p.lookup "div_2by1" = some div2by1) (hpm : p.lookup "div_submul" = some divSubmul)
    (hpk : p.lookup "div_kstep" = some divKstep) (n : Nat) (s₀ : St) (h : DkInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n dkLoop ⦃fun r s' => DkPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    have h' := h
    simp only [DkInv, KBase] at h'
    simp only [DkPost]
    rw [exec, step_while (w := dkLoop) rfl]
    vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64, ih,
      divKstep_spec p hpl hpc hpa hp2 hpm hpk n]
    all_goals clear ih
    all_goals (try simp only [DkPost, KBase] at *)
    all_goals (try simp only [DkInv, KBase] at ⊢)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_cons, St.setLocs_nil,
      Cmp.eval, BinOp.eval, Nat.reduceEqDiff, reduceIte, decide_eq_true_eq] at *)
    all_goals (try and_intros)
    all_goals first
      | (grind (splits := 20) [arena_grind, lang_grind]; done)
      | (apply dk_pre_goal Pg C _ h <;> grind)
      | apply dk_same_goal Pg C _ _ _ h
      | apply dk_rem_goal Pg C _ _ _ h
      | apply dk_eq_goal Pg C _ _ _ h
    all_goals (try simp only [DkStep])
    all_goals (try and_intros)
    all_goals grind [lang_grind, arena_grind]

theorem dkLoop_step_spec (hpl : p.lookup "nat_limb" = some natLimb)
    (hpc : p.lookup "add_carry" = some addCarry) (hpa : p.lookup "div_add" = some divAdd)
    (hp2 : p.lookup "div_2by1" = some div2by1) (hpm : p.lookup "div_submul" = some divSubmul)
    (hpk : p.lookup "div_kstep" = some divKstep) (n : Nat) (s₀ : St) (h : DkInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) dkLoop ⦃fun r s' => DkPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (dkLoop_spec p Pg C hpl hpc hpa hp2 hpm hpk (n + 1) s₀ h)

end dk

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
  mod1 : p.lookup "div_mod1" = some divMod1
  modk : p.lookup "div_modk" = some divModK
  trim : p.lookup "nat_trim" = some natTrim
  divmod : p.lookup "nat_divmod" = some natDivmod

section specs
variable (p : Prog) (hf : DivFns p)

/-- A dividend shorter than the normalised divisor is below it. -/
theorem pv_lt_of_short (P : Array Word) (oa la ob lb : Nat) (hl : la < lb) (hn : Norm P ob lb) :
    pv P oa la < pv P ob lb := by
  have h1 := pv_lt_wt P oa la
  have h2 := pv_ge_wt P ob lb (by omega) hn
  have h3 : wt la ≤ wt (lb - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem div_short (P : Array Word) (oa la ob lb : Nat) (hl : la < lb) (hn : Norm P ob lb) :
    pv P oa la / pv P ob lb = 0 := Nat.div_eq_of_lt (pv_lt_of_short P oa la ob lb hl hn)

theorem mod_short (P : Array Word) (oa la ob lb : Nat) (hl : la < lb) (hn : Norm P ob lb) :
    pv P oa la % pv P ob lb = pv P oa la := Nat.mod_eq_of_lt (pv_lt_of_short P oa la ob lb hl hn)

/-- A left shift that does not overflow multiplies. -/
theorem shl_mul (x s : Word) (hs : s.toNat ≤ 63) (h : x.toNat * sh s.toNat < 2 ^ 64) :
    (x <<< s).toNat = x.toNat * sh s.toNat := by
  rw [shl_lo x s (by omega)]; exact Nat.mod_eq_of_lt h
grind_pattern [arena_grind] shl_mul => (x <<< s).toNat, x.toNat * sh s.toNat

/-- A right shift by `s ≤ 63` divides by `2^s`. -/
theorem shr_div (r s : Word) (hs : s.toNat ≤ 63) : (r >>> s).toNat = r.toNat / sh s.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.mod_eq_of_lt (by omega : s.toNat < 64),
    Nat.shiftRight_eq_div_pow]; rfl
grind_pattern [arena_grind] shr_div => (r >>> s).toNat, sh s.toNat

/-- A tier-decoded load of a one-limb slice in the pool is the slice's value. -/
theorem ld_pv1 (m : Mem) (x : Word) (h : (x &&& 1099511627775).toNat < (m.arr64 (tierA POOL (x >>> 40))).size)
    (h' : x.toNat < 2 ^ 41) :
    (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat].toNat = pv (vpool m) x.toNat 1 := by
  rw [vpool_ld m x h (by rw [vpool_size]; exact h'), pv_one _ _ (by rw [vpool_size]; exact h')]
grind_pattern [arena_grind] ld_pv1 => (m.arr64 (tierA POOL (x >>> 40)))[(x &&& 1099511627775).toNat], vpool m

/-- The one-limb division's result: `A · 2^s = Q · (b0 · 2^s) + R` with `R` a multiple of `2^s`
below `b0 · 2^s`. -/
theorem d1_quot (A Q D b0 S R : Nat) (h : A * S = Q * D + R) (hD : D = b0 * S) (hd : S ∣ R)
    (hr : R < D) : A / b0 = Q := by
  obtain ⟨t, rfl⟩ := hd
  subst hD
  have hS : 0 < S := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
  have h1 : A = Q * b0 + t := by
    apply Nat.eq_of_mul_eq_mul_right hS; grind
  have h2 : t < b0 := by
    apply Nat.lt_of_mul_lt_mul_left (a := S); grind
  apply div_of_bounds <;> grind
grind_pattern [natop_grind] d1_quot => A * S, Q * D, S ∣ R, b0 * S

theorem d1_rem (A Q D b0 S R : Nat) (h : A * S = Q * D + R) (hD : D = b0 * S) (hd : S ∣ R)
    (hr : R < D) : A % b0 = R / S := by
  have hq := d1_quot A Q D b0 S R h hD hd hr
  obtain ⟨t, rfl⟩ := hd
  subst hD
  have hS : 0 < S := Nat.pos_of_ne_zero (by rintro rfl; simp at hr)
  have h1 : A = Q * b0 + t := by
    apply Nat.eq_of_mul_eq_mul_right hS; grind
  have h2 : t < b0 := by
    apply Nat.lt_of_mul_lt_mul_left (a := S); grind
  rw [Nat.mul_div_cancel_left _ hS, mod_of_bounds A b0 Q (by omega) (by omega)]; omega
grind_pattern [natop_grind] d1_rem => A * S, Q * D, S ∣ R, b0 * S

/-- The quotient of `div_mod1`, in the shape of its verification condition (`s` the state after
the loop, `rs` the trim of the quotient). -/
theorem d1_quot_goal (m₀ : Mem) (s : St) (rs : List Word) (oa la ob : Word)
    (h11 : s.loc 11 = s.loc 3 >>> 40) (h12 : s.loc 12 = s.loc 3 &&& 1099511627775)
    (hT : (s.loc 3).toNat < 2 ^ 41) (hs : (s.mem.arr64 (tierA POOL (s.loc 11))).size ≤ 2 ^ 40)
    (hst : (s.loc 12 + s.loc 1).toNat < (s.mem.arr64 (tierA POOL (s.loc 11))).size)
    (hk : (s.loc 12).toNat + (s.loc 1).toNat < 2 ^ 40) (hla : s.loc 1 = la)
    (htr : pv (vpool (s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + s.loc 1) (s.loc 7 >>> s.loc 8)))
        (s.loc 3).toNat (rs.headD 0).toNat =
      pv (vpool (s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + s.loc 1) (s.loc 7 >>> s.loc 8)))
        (s.loc 3).toNat (s.loc 1).toNat)
    (heq : pv (vpool m₀) oa.toNat la.toNat * sh (s.loc 8).toNat =
      pv (vpool s.mem) (s.loc 3).toNat la.toNat * (s.loc 9).toNat + (s.loc 7).toNat)
    (hD : (s.loc 9).toNat = pv (vpool m₀) ob.toNat 1 * sh (s.loc 8).toNat)
    (hdv : sh (s.loc 8).toNat ∣ (s.loc 7).toNat) (hr : (s.loc 7).toNat < (s.loc 9).toNat) :
    pv (vpool ((s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + s.loc 1) (s.loc 7 >>> s.loc 8)).set64
        CTL 0 (s.loc 3 + s.loc 1 + 1))) (s.loc 3).toNat (rs.headD 0).toNat =
      pv (vpool m₀) oa.toNat la.toNat / pv (vpool m₀) ob.toNat 1 := by
  rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, htr]
  rw [h11, h12] at hst ⊢
  rw [h11] at hs
  rw [h12, tag_idx_toNat] at hk
  rw [vpool_stidx s.mem (s.loc 3) (s.loc 1) _ hT hst hs (by rw [tag_idx_toNat]; omega),
    pv_set_above (k := (s.loc 1).toNat) (j := (s.loc 3 + s.loc 1).toNat)
      (h := by rw [UInt64.toNat_add]; omega), hla]
  exact (d1_quot _ _ _ _ _ _ heq hD hdv hr).symm

/-- The remainder of `div_mod1`, likewise (`rs` the trim of the remainder limb). -/
theorem d1_rem_goal (m₀ : Mem) (s : St) (rs : List Word) (oa la ob : Word)
    (h11 : s.loc 11 = s.loc 3 >>> 40) (h12 : s.loc 12 = s.loc 3 &&& 1099511627775)
    (hT : (s.loc 3).toNat < 2 ^ 41) (hs : (s.mem.arr64 (tierA POOL (s.loc 11))).size ≤ 2 ^ 40)
    (hst : (s.loc 12 + s.loc 1).toNat < (s.mem.arr64 (tierA POOL (s.loc 11))).size)
    (hk : (s.loc 12).toNat + (s.loc 1).toNat < 2 ^ 40)
    (hs63 : (s.loc 8).toNat ≤ 63)
    (htr : pv (vpool (s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + s.loc 1) (s.loc 7 >>> s.loc 8)))
        (s.loc 3 + s.loc 1).toNat (rs.headD 0).toNat =
      pv (vpool (s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + s.loc 1) (s.loc 7 >>> s.loc 8)))
        (s.loc 3 + s.loc 1).toNat 1)
    (heq : pv (vpool m₀) oa.toNat la.toNat * sh (s.loc 8).toNat =
      pv (vpool s.mem) (s.loc 3).toNat la.toNat * (s.loc 9).toNat + (s.loc 7).toNat)
    (hD : (s.loc 9).toNat = pv (vpool m₀) ob.toNat 1 * sh (s.loc 8).toNat)
    (hdv : sh (s.loc 8).toNat ∣ (s.loc 7).toNat) (hr : (s.loc 7).toNat < (s.loc 9).toNat) :
    pv (vpool ((s.mem.set64 (tierA POOL (s.loc 11)) (s.loc 12 + s.loc 1) (s.loc 7 >>> s.loc 8)).set64
        CTL 0 (s.loc 3 + s.loc 1 + 1))) (s.loc 3 + s.loc 1).toNat (rs.headD 0).toNat =
      pv (vpool m₀) oa.toNat la.toNat % pv (vpool m₀) ob.toNat 1 := by
  rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, htr]
  rw [h11, h12] at hst ⊢
  rw [h11] at hs
  rw [h12, tag_idx_toNat] at hk
  have hvs := vpool_size s.mem
  have e : (s.loc 3 + s.loc 1).toNat = (s.loc 3).toNat + (s.loc 1).toNat := by
    rw [UInt64.toNat_add]; omega
  rw [vpool_stidx s.mem (s.loc 3) (s.loc 1) _ hT hst hs (by rw [tag_idx_toNat]; omega),
    pv_one _ _ (by rw [Array.size_set!, hvs]; omega)]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds_self]
  rw [shr_div _ _ hs63]
  exact (d1_rem _ _ _ _ _ _ heq hD hdv hr).symm

set_option maxHeartbeats 4000000 in
include hf in
/-- `div_mod1`: `nat_divmod` for a one-limb divisor `b ≠ 0`. -/
theorem divMod1_spec (n : Nat) (s₀ : St) (oa la ob : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob 1)
    (hnb : Norm (vpool s₀.mem) ob.toNat 1) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_mod1" [oa, la, ob]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat / pv (vpool s₀.mem) ob.toNat 1 ∧
      SliceOK s'.mem (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat % pv (vpool s₀.mem) ob.toNat 1; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hok2 := hok.ctl; have hok3 := hok.cap; have hok4 := hok.top; have hok6 := hok.inTier
  clear hok
  have ha1 := ha.1
  have hb1 := hb.1
  rw [invoke_eq _ hf.mod1]
  simp only [callFn, divMod1]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      divNorm_spec p hf.norm n, divRecip_spec p hf.d2by1 hf.recip n,
      d1Loop_step_spec p hf.d2by1 (vpool s₀.mem) (pcap s₀.mem) (pv (vpool s₀.mem) ob.toNat 1) n,
      natTrim_spec p hf.trim n]
    all_goals (try simp only [D1Inv, D1Post] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, L.Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte,
      Nat.reduceEqDiff, UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals (try and_intros)
    all_goals (try simp only [vpool_size] at *)
    all_goals (try exact Agree.refl _ _)
    all_goals (try exact True.intro)
    all_goals (try exact Nat.dvd_zero _)
    all_goals (try (grind (splits := 20) [arena_grind, lang_grind]; done))
    all_goals (try (rw [shl_mul _ _ (by grind) (by grind)]; exact Nat.dvd_mul_left _ _))
    all_goals first
      | (apply d1_quot_goal <;> grind)
      | (apply d1_rem_goal <;> grind)

/-- `b`'s top two limbs read shifted by `s` (`div_modk`'s `d`): `⌊b 2^s / 2^(64 (lb - 1))⌋`, and
at least `2^63` when the top limb shifted is. -/
theorem kd_val (m : Mem) (P : Array Word) (ob lb s : Word) (hlb : 2 ≤ lb.toNat)
    (hob : ob.toNat + lb.toNat < 2 ^ 41) (hs : s.toNat ≤ 63)
    (hl1 : ((ob + lb - 1) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((ob + lb - 1) >>> 40))).size)
    (hl2 : ((ob + lb - 2) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((ob + lb - 2) >>> 40))).size)
    (hfit : (m.arr64 (tierA POOL ((ob + lb - 1) >>> 40)))[((ob + lb - 1) &&& 1099511627775).toNat].toNat *
      sh s.toNat < 2 ^ 64)
    (hb : pv (vpool m) ob.toNat lb.toNat = pv P ob.toNat lb.toNat) :
    ((m.arr64 (tierA POOL ((ob + lb - 1) >>> 40)))[((ob + lb - 1) &&& 1099511627775).toNat] <<< s +
      ((m.arr64 (tierA POOL ((ob + lb - 2) >>> 40)))[((ob + lb - 2) &&& 1099511627775).toNat] >>> 1 >>>
        (63 - s))).toNat =
      pv P ob.toNat lb.toNat * sh s.toNat / wt (lb.toNat - 1) := by
  have hvs := vpool_size m
  have e1 : (ob + lb - 1).toNat = ob.toNat + lb.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega),
      UInt64.toNat_add, UInt64.toNat_one]; omega
  have e2 : (ob + lb - 2).toNat = ob.toNat + lb.toNat - 2 := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega),
      UInt64.toNat_add]; simp; omega
  rw [vpool_ld m _ hl1 (by omega), vpool_ld m _ hl2 (by omega)] at *
  simp only [e1, e2] at *
  generalize hx1 : (vpool m)[ob.toNat + lb.toNat - 1] = x1 at *
  generalize hx2 : (vpool m)[ob.toNat + lb.toNat - 2] = x2 at *
  have hdec : pv (vpool m) ob.toNat lb.toNat =
      pv (vpool m) ob.toNat (lb.toNat - 2) + wt (lb.toNat - 2) * (x2.toNat + 2 ^ 64 * x1.toNat) := by
    have h1 := pv_succ (vpool m) ob.toNat (lb.toNat - 1) lb.toNat (ob.toNat + lb.toNat - 1)
      (by omega) (by omega) (by omega)
    have h2 := pv_succ (vpool m) ob.toNat (lb.toNat - 2) (lb.toNat - 1) (ob.toNat + lb.toNat - 2)
      (by omega) (by omega) (by omega)
    rw [h1, h2, hx1, hx2, wt_succ (lb.toNat - 2) (lb.toNat - 1) (by omega)]
    grind
  rw [← hb, hdec, show lb.toNat - 1 = lb.toNat - 2 + 1 by omega,
    top2_div _ _ _ _ _ (pv_lt_wt _ _ _) hs]
  have hlo := shl_hi x2 s (by omega)
  have hlt := shl_hi_lt' x2 s (by omega)
  have hhi := shl_mul x1 s hs hfit
  have hroom := mod_shift_room x1.toNat s.toNat hs
  rw [Nat.mod_eq_of_lt hfit] at hroom
  rw [UInt64.toNat_add, hhi, hlo, Nat.mod_eq_of_lt (by rw [← hlo]; omega)]; rfl

/-- The shifted top word of `b` (`div_modk`'s `d`) as numbers. -/
theorem kd_word (x1 x2 s : Word) (hs : s.toNat ≤ 63) (hfit : x1.toNat * sh s.toNat < 2 ^ 64) :
    ((x1 <<< s) + ((x2 >>> 1) >>> (63 - s))).toNat =
      x1.toNat * sh s.toNat + x2.toNat * sh s.toNat / 2 ^ 64 := by
  have hlo := shl_hi x2 s (by omega)
  have hlt := shl_hi_lt' x2 s (by omega)
  have hhi := shl_mul x1 s hs hfit
  have hroom := mod_shift_room x1.toNat s.toNat hs
  rw [Nat.mod_eq_of_lt hfit] at hroom
  rw [UInt64.toNat_add, hhi, hlo, Nat.mod_eq_of_lt (by rw [← hlo]; omega)]; rfl

theorem kd_ge (x1 x2 s : Word) (hs : s.toNat ≤ 63) (hfit : x1.toNat * sh s.toNat < 2 ^ 64)
    (hn : 2 ^ 63 ≤ x1.toNat * sh s.toNat) : 2 ^ 63 ≤ ((x1 <<< s) + ((x2 >>> 1) >>> (63 - s))).toNat := by
  rw [kd_word x1 x2 s hs hfit]; omega

theorem kd_pos (x1 x2 s : Word) (hs : s.toNat ≤ 63) (hfit : x1.toNat * sh s.toNat < 2 ^ 64)
    (hn : 2 ^ 63 ≤ x1.toNat * sh s.toNat) : 0 < ((x1 <<< s) + ((x2 >>> 1) >>> (63 - s))).toNat := by
  have := kd_ge x1 x2 s hs hfit hn; omega

/-- `b`'s top limb, loaded, is nonzero. -/
theorem kd_top_pos (m : Mem) (ob lb : Word) (hlb : 2 ≤ lb.toNat) (hob : ob.toNat + lb.toNat < 2 ^ 41)
    (hl1 : ((ob + lb - 1) &&& 1099511627775).toNat < (m.arr64 (tierA POOL ((ob + lb - 1) >>> 40))).size)
    (hn : Norm (vpool m) ob.toNat lb.toNat) :
    0 < (m.arr64 (tierA POOL ((ob + lb - 1) >>> 40)))[((ob + lb - 1) &&& 1099511627775).toNat].toNat := by
  have hvs := vpool_size m
  have e1 : (ob + lb - 1).toNat = ob.toNat + (lb.toNat - 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, UInt64.toNat_add]; simp; omega),
      UInt64.toNat_add, UInt64.toNat_one]; omega
  rw [vpool_ld m _ hl1 (by omega)]
  simp only [e1]
  have := hn (by omega)
  rw [Array.getElem?_eq_getElem (by omega)] at this
  simp only [Option.getD_some] at this
  rcases Nat.eq_zero_or_pos (vpool m)[ob.toNat + (lb.toNat - 1)].toNat with h0 | h0
  · exact absurd (UInt64.toNat_inj.mp (by simpa using h0)) this
  · exact h0

theorem Same.pv_off {p q : Array Word} {o o' n : Nat} (h : Same p q o o' n) (k j : Nat)
    (hk : k + j ≤ n) : L.Arena.pv p (o + k) j = L.Arena.pv q (o' + k) j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [L.Arena.pv, ih (by omega)]
    have := h (k + j) (by omega)
    rw [show o + k + j = o + (k + j) by omega, show o' + k + j = o' + (k + j) by omega, this]

/-- The zero limb on top of the copy, as a store into the virtual pool at `w + la`. -/
theorem kinit_store (P : Array Word) (s : St) (hk : KBase P (pcap s.mem) s) :
    vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 1)) 0) =
      (vpool s.mem).set! ((s.loc 6).toNat + (s.loc 1).toNat) 0 := by
  obtain ⟨_, _, _, _, h14, h15, hroom, hsz, _, hT, h41, _, h6, _⟩ := hk
  have hroom' := hroom
  rw [h15, tag_idx_toNat] at hroom'
  have e : (s.loc 5 + s.loc 1).toNat = (s.loc 5).toNat + (s.loc 1).toNat := by
    rw [UInt64.toNat_add]; omega
  rw [h14] at hsz hroom hroom'
  rw [h14, h15, vpool_stidx s.mem (s.loc 4) (s.loc 5 + s.loc 1) 0 hT
    (by rw [UInt64.toNat_add, e, tag_idx_toNat]; omega) hsz (by rw [tag_idx_toNat, e]; omega)]
  congr 1
  rw [UInt64.toNat_add, e]; omega

/-- The first window of Knuth's loop: `a`'s top `lb - 1` limbs and a zero limb. -/
theorem kinit_R (P : Array Word) (s : St) (hk : KBase P (pcap s.mem) s)
    (hsame : Same (vpool s.mem) P (s.loc 6).toNat (s.loc 0).toNat (s.loc 1).toNat) :
    pv (vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 1)) 0))
        ((s.loc 6).toNat + (s.loc 5).toNat) (s.loc 3).toNat =
      pv P ((s.loc 0).toNat + (s.loc 5).toNat) ((s.loc 3).toNat - 1) := by
  rw [kinit_store P s hk]
  obtain ⟨_, hP, _, _, _, _, _, _, _, hT, h41, _, h6, hn, hlb, _⟩ := hk
  have hvs := vpool_size s.mem
  have e3 : (s.loc 3).toNat = (s.loc 3).toNat - 1 + 1 := by omega
  conv => lhs; rw [e3]
  rw [pv_set_succ (vpool s.mem) _ ((s.loc 3).toNat - 1) _ _ _ rfl (by omega) (by omega),
    hsame.pv_off _ _ (by omega)]
  simp

theorem kinit_same (P : Array Word) (s : St) (hk : KBase P (pcap s.mem) s)
    (hsame : Same (vpool s.mem) P (s.loc 6).toNat (s.loc 0).toNat (s.loc 1).toNat) :
    Same (vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 1)) 0)) P
      (s.loc 6).toNat (s.loc 0).toNat (s.loc 5).toNat := by
  rw [kinit_store P s hk]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hn, hlb, _⟩ := hk
  exact (hsame.set_above _ _ (by omega)).mono (by omega)

theorem kinit_lt (P : Array Word) (s : St) (ob lb : Word) (hk : KBase P (pcap s.mem) s)
    (hsame : Same (vpool s.mem) P (s.loc 6).toNat (s.loc 0).toNat (s.loc 1).toNat)
    (h2 : s.loc 2 = ob) (h3 : s.loc 3 = lb) (hn : Norm P ob.toNat lb.toNat) :
    pv (vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 1)) 0))
        ((s.loc 6).toNat + (s.loc 5).toNat) (s.loc 3).toNat < pv P ob.toNat lb.toNat := by
  rw [kinit_R P s hk hsame]
  have hl := hk.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  subst h2 h3
  have := pv_lt_wt P ((s.loc 0).toNat + (s.loc 5).toNat) ((s.loc 3).toNat - 1)
  have := pv_ge_wt P (s.loc 2).toNat (s.loc 3).toNat (by omega) hn
  omega

theorem kinit_eq (P : Array Word) (s : St) (hk : KBase P (pcap s.mem) s)
    (hsame : Same (vpool s.mem) P (s.loc 6).toNat (s.loc 0).toNat (s.loc 1).toNat) (b : Nat) :
    pv P (s.loc 0).toNat (s.loc 1).toNat =
      pv P (s.loc 0).toNat (s.loc 5).toNat + wt (s.loc 5).toNat *
        (pv (vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 1)) 0))
            ((s.loc 4).toNat + (s.loc 5).toNat) ((s.loc 5).toNat - (s.loc 5).toNat) * b +
          pv (vpool (s.mem.set64 (tierA POOL (s.loc 14)) (s.loc 15 + (s.loc 5 + s.loc 1)) 0))
            ((s.loc 6).toNat + (s.loc 5).toNat) (s.loc 3).toNat) := by
  rw [kinit_R P s hk hsame]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hn, hlb, _⟩ := hk
  rw [Nat.sub_self, show pv _ _ 0 = 0 from rfl, Nat.zero_mul, Nat.zero_add, ← pv_append,
    show (s.loc 5).toNat + ((s.loc 3).toNat - 1) = (s.loc 1).toNat by omega]

/-- The results of `div_modk`, from Knuth's loop's post (`a = Q b + R`, `R < b`; `sd` the state
after the loop, `rs` the trim). -/
theorem kfin_q (sd : St) (rs : List Word) (A b : Nat)
    (htr : pv (vpool sd.mem) (sd.loc 4).toNat (rs.headD 0).toNat =
      pv (vpool sd.mem) (sd.loc 4).toNat (sd.loc 5).toNat)
    (heq : A = pv (vpool sd.mem) (sd.loc 4).toNat (sd.loc 5).toNat * b +
      pv (vpool sd.mem) (sd.loc 6).toNat (sd.loc 3).toNat)
    (hR : pv (vpool sd.mem) (sd.loc 6).toNat (sd.loc 3).toNat < b) :
    pv (vpool (sd.mem.set64 CTL 0 (sd.loc 6 + sd.loc 3))) (sd.loc 4).toNat (rs.headD 0).toNat =
      A / b := by
  rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, htr]
  exact (div_of_bounds _ _ _ (by omega) (by omega)).symm

theorem kfin_r (sd : St) (rs : List Word) (A b : Nat)
    (htr : pv (vpool sd.mem) (sd.loc 6).toNat (rs.headD 0).toNat =
      pv (vpool sd.mem) (sd.loc 6).toNat (sd.loc 3).toNat)
    (heq : A = pv (vpool sd.mem) (sd.loc 4).toNat (sd.loc 5).toNat * b +
      pv (vpool sd.mem) (sd.loc 6).toNat (sd.loc 3).toNat)
    (hR : pv (vpool sd.mem) (sd.loc 6).toNat (sd.loc 3).toNat < b) :
    pv (vpool (sd.mem.set64 CTL 0 (sd.loc 6 + sd.loc 3))) (sd.loc 6).toNat (rs.headD 0).toNat =
      A % b := by
  rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, htr]
  rw [mod_of_bounds _ _ (pv (vpool sd.mem) (sd.loc 4).toNat (sd.loc 5).toNat) (by omega) (by omega)]
  omega

set_option maxHeartbeats 8000000 in
include hf in
/-- `div_modk`: `nat_divmod` for `2 ≤ lb ≤ la`. -/
theorem divModK_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) (h2 : 2 ≤ lb.toNat) (hl : lb.toNat ≤ la.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "div_modk" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PoolOK s'.mem ∧ Grows s₀.mem s'.mem ∧
      SliceOK s'.mem (r.headD 0) (r.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.headD 0).toNat (r.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat / pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      SliceOK s'.mem (r.tail.tail.headD 0) (r.tail.tail.tail.headD 0) ∧
      Norm (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat ∧
      pv (vpool s'.mem) (r.tail.tail.headD 0).toNat (r.tail.tail.tail.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat % pv (vpool s₀.mem) ob.toNat lb.toNat; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  have hok2 := hok.ctl; have hok3 := hok.cap; have hok4 := hok.top; have hok6 := hok.inTier
  clear hok
  have ha1 := ha.1
  have hb1 := hb.1
  rw [invoke_eq _ hf.modk]
  simp only [callFn, divModK]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      divNorm_spec p hf.norm n, divRecip_spec p hf.d2by1 hf.recip n,
      dcpLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n,
      dkLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) hf.limb hf.carry hf.add hf.d2by1 hf.submul
        hf.kstep n,
      natTrim_spec p hf.trim n]
    all_goals (try simp only [DcpInv, DcpPost, DkInv, DkPost, KBase] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, St.setLocs_nil, St.setLocs_cons,
      List.headD_cons, List.tail_cons, L.Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte,
      Nat.reduceEqDiff, UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals (try and_intros)
    all_goals (try simp only [vpool_size] at *)
    all_goals (try exact Agree.refl _ _)
    all_goals (try exact True.intro)
    all_goals (try exact Same.zero _ _ _ _)
    all_goals first
      | (grind (splits := 20) [arena_grind, lang_grind]; done)
      | apply kd_val
      | apply kd_pos
      | apply kd_ge
      | apply kd_top_pos
      | apply kinit_same
      | apply kinit_lt
      | apply kinit_eq
      | apply kfin_q
      | apply kfin_r
      | skip
    all_goals (try (grind (splits := 20) [arena_grind, lang_grind]; done))
    all_goals (try (grind (splits := 20) [arena_grind, lang_grind, kd_val, kd_pos]; done))
    all_goals (try simp only [KBase])
    all_goals (try and_intros)
    all_goals grind (splits := 20) [arena_grind, lang_grind]

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
  have hcap := hok.cap
  have htop := hok.top
  have ha1 := ha.1
  have hb1 := hb.1
  rw [invoke_eq _ hf.divmod]
  simp only [callFn, natDivmod]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64,
      natTrim_spec p hf.trim n, divMod1_spec p hf n, divModK_spec p hf n]
    all_goals (try simp only [St.setLoc_loc, L.St.setLoc_mem, List.headD_cons, List.tail_cons,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval,
      reduceIte, Nat.reduceEqDiff, UInt64.toNat_zero, Sig.retVal, Sig.retOr] at *)
    all_goals grind [arena_grind, lang_grind, natcmp_grind, natop_grind, div_short, mod_short]

end specs

end L.Arena
