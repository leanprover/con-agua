module

meta import ConAgua.L.Semantics
meta import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatAdd
public import ConAgua.Arena.NatShiftFacts
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatCmpFacts
import ConAgua.Arena.NatGrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas
import ConAgua.Front.Preserve

@[expose] public section

/-!
# `Nat.shiftRight` on the limb pool: `nat_shr`

`nat_shr(oa, la, ob, lb)` is `a >>> b = a / 2^b` for two pool slices, `b` normalised (con-ron's
`shift_right_nat`, `skip_index`, `shr_from`, `shr_bits_from`, `ron/nat.rs:406-462`). An amount of
two or more limbs is at least `2^64`, so the result is `0` (for `la < 2^57`, which every pool
satisfies; above that, `abort`). Otherwise `k = b[0]`: skip `w = k >> 6` limbs (if that is all of
`a`, the result is `0`), then one pass over the remaining slice `(oa + w, la - w)`, limb `i` of the
result being `(x >> s) | ((y << 1) << (63 - s))` with `x`, `y` limbs `i`, `i + 1` and `s = k & 63`
(branch-free, as in `nat_shl`: the second part is `y << (64 - s)` for `s ≥ 1` and `0` for
`s = 0`), then `nat_trim`.

The loop runs over the shifted slice, so `w` does not occur in its invariant: the result so far
times `2^s`, plus the low `s` bits of the slice's first limb, is the slice's first `i` limbs plus
the low `s` bits of limb `i`, weighted (`ShrInv`). `shr_split` is its digit equation. The skipped
limbs and the division are three lemmas at the end (`shr_val`, `shr_big_w`, `shr_big_b`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Word facts -/

/-- The low `s` bits of `x`, as a named function (an atom to `grind`). -/
def lowb (x s : Nat) : Nat := x % 2 ^ s

theorem lowb_lt (x s : Nat) : lowb x s < sh s := Nat.mod_lt _ (Nat.two_pow_pos _)
grind_pattern [arena_grind] lowb_lt => lowb x s

@[arena_grind =] theorem lowb_zero (s : Nat) : lowb 0 s = 0 := Nat.zero_mod _

theorem shr_hi (y b : Word) (hb : b.toNat < 64) :
    ((y <<< 1) <<< (63 - b)).toNat = (y.toNat % 2 ^ b.toNat) * 2 ^ (64 - b.toNat) := by
  have h63 : (63 - b).toNat = 63 - b.toNat := by grind
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_shiftLeft, h63]
  simp only [Nat.shiftLeft_eq, UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega : 63 - b.toNat < 64), Nat.mod_eq_of_lt (by omega : 1 < 64)]
  rw [Nat.mod_mul_mod, Nat.mul_assoc, ← Nat.pow_add, show 1 + (63 - b.toNat) = 64 - b.toNat by omega]
  have : 2 ^ 64 = 2 ^ b.toNat * 2 ^ (64 - b.toNat) := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_mod_mul_right]

/-- The digit equation of one limb of the right shift. -/
theorem shr_split (x y b : Word) (hb : b.toNat < 64) :
    ((x >>> b) ||| ((y <<< 1) <<< (63 - b))).toNat * sh b.toNat + lowb x.toNat b.toNat =
      x.toNat + lowb y.toNat b.toNat * 2 ^ 64 := by
  rw [UInt64.toNat_or, shr_hi y b hb, UInt64.toNat_shiftRight, Nat.mod_eq_of_lt hb,
    Nat.shiftRight_eq_div_pow]
  have hlt : x.toNat / 2 ^ b.toNat < 2 ^ (64 - b.toNat) := by
    apply Nat.div_lt_of_lt_mul
    rw [← Nat.pow_add, show b.toNat + (64 - b.toNat) = 64 by omega]; exact x.toNat_lt
  rw [← Nat.shiftLeft_eq, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq]
  simp only [sh, lowb]
  have h2 : 2 ^ (64 - b.toNat) * 2 ^ b.toNat = 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; omega
  have := Nat.div_add_mod x.toNat (2 ^ b.toNat)
  rw [Nat.add_mul, Nat.mul_assoc, h2]
  rw [Nat.mul_comm (x.toNat / 2 ^ b.toNat)]
  omega
grind_pattern [arena_grind] shr_split => (x >>> b) ||| ((y <<< 1) <<< (63 - b))

/-! ## The division at the end -/

/-- The shift that skips `w < la` limbs: the quotient is what the loop computed. -/
theorem shr_val (P : Array Word) (oa la w o l S R : Nat) (ho : o = oa + w) (hl : l = la - w)
    (hw : w < la) (h1 : R * S ≤ pv P o l) (h2 : pv P o l < R * S + S) :
    pv P oa la / (S * wt w) = R := by
  have hA := pv_append P oa w (la - w)
  rw [show w + (la - w) = la by omega] at hA
  subst ho hl
  have h3 := pv_lt_wt P oa w
  have hS : 0 < S := by
    rcases Nat.eq_zero_or_pos S with h | h
    · subst h; omega
    · exact h
  have m1 : wt w * (R * S) ≤ wt w * pv P (oa + w) (la - w) := Nat.mul_le_mul_left _ h1
  have m2 : wt w * pv P (oa + w) (la - w) + wt w ≤ wt w * (R * S + S) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h2
  apply Nat.div_eq_of_lt_le <;> grind

/-- The quotient by an amount `b = k` of at most one limb that skips `w = k >> 6 < la` limbs, in
the shape the loop's post gives (`ShrPost`). Every variable of the pattern is bound by a term of
that post, so it fires about once (DESIGN.md, "Slow declarations": `shr_val`'s own pattern
`pv P oa la / (S * wt w), pv P o l, R * S` matched every `pv` and every product). -/
theorem shr_small (P Q R : Array Word) (oa la ob lb o l t r : Nat) (k : Word)
    (hk : pv Q ob lb = k.toNat) (ho : o = oa + (k >>> 6).toNat) (hl : l = la - (k >>> 6).toNat)
    (hw : (k >>> 6).toNat < la)
    (h : pv R t r * sh (k &&& 63).toNat + lowb (lv P o l 0) (k &&& 63).toNat = pv P o l) :
    pv P oa la / 2 ^ pv Q ob lb = pv R t r := by
  rw [hk, shamt]
  exact shr_val P oa la _ o l _ _ ho hl hw (by omega)
    (by have := lowb_lt (lv P o l 0) (k &&& 63).toNat; omega)
grind_pattern [natop_grind] shr_small => pv P oa la / 2 ^ pv Q ob lb,
  pv R t r * sh (k &&& 63).toNat, lowb (lv P o l 0) (k &&& 63).toNat

/-- Skipping all of `a`: the quotient is `0`. -/
theorem shr_big_w (P : Array Word) (oa la w S : Nat) (hw : la ≤ w) (hS : 0 < S) :
    pv P oa la / (S * wt w) = 0 := by
  apply Nat.div_eq_of_lt
  have := pv_lt_wt P oa la
  have : wt la ≤ wt w := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hw)
  have : wt w ≤ S * wt w := Nat.le_mul_of_pos_left _ hS
  omega
grind_pattern [natop_grind] shr_big_w => pv P oa la / (S * wt w)

/-- An amount of two or more limbs: the quotient is `0`. -/
theorem shr_big_b (P Q : Array Word) (oa la ob lb : Nat) (hn : Norm Q ob lb) (hl : 2 ≤ lb)
    (hla : la < 2 ^ 57) : pv P oa la / 2 ^ pv Q ob lb = 0 := by
  apply Nat.div_eq_of_lt
  have h1 := pv_lt_wt P oa la
  have h2 := pv_ge_wt Q ob lb (by omega) hn
  have h3 : wt 1 ≤ wt (lb - 1) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ (by omega))
  have h4 : 64 * la < pv Q ob lb := by
    have : wt 1 = 2 ^ 64 := rfl
    omega
  exact Nat.lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt h4))
grind_pattern [natop_grind] shr_big_b => pv P oa la / 2 ^ pv Q ob lb, Norm Q ob lb

/-! ## `nat_shr(oa, la, ob, lb)` -/

/-- One pass over the shifted slice `(oa, n)` (`oa` already moved past the skipped limbs, its
tier and index in `ta`, `qa`), but its last limb: limb `i` of the result is `x >> b` with the low
bits of limb `i + 1` (`rb = 63 - b`). -/
def shrLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, b, i, x, y, pt, pb, ta, qa, rb) {
  for i < w {
    y := POOL⟨ta⟩[qa + i + 1];
    POOL⟨pt⟩[pb + i] := (x >> b) | ((y << 1) << rb);
    x := y
  }
}

/-- The slice resolved to tier and index once, one pass, the last limb, `nat_trim`. No call but
`nat_trim`, which the inliner inlines: the compiled function is a leaf (lane linleaf).
con-ron: ConRon/Arena/Core.lean:1152-1185 ConRon.Arena.natBinOpResult -/
@[no_expose, l_impl ConRon.Arena.natBinOpResult]
def natShr : FunDecl := lfn (oa, la, ob, lb) locals (top, n, w, b, i, x, y, pt, pb, ta, qa, rb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if lb < 2 {
    if lb == 1 { w := POOL⦃ob⦄ };
    b := w & 63;
    w := w >> 6;
    if w < la {
      oa := oa + w;
      n := la - w;
      if len(POOL⟨pt⟩) - pb < n { abort };
      ta := ⦃oa⦄.tier;
      qa := ⦃oa⦄.idx;
      rb := 63 - b;
      x := POOL⟨ta⟩[qa];
      w := n - 1;
      ⟪shrLoop⟫;
      POOL⟨pt⟩[pb + w] := x >> b;
      n := call nat_trim(top, n)
    }
  } else {
    if 144115188075855872 <= la { abort }
  };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_shr`. -/
def natShrProg : Prog := natProg ++ [("nat_shr", natShr)]

/- `[0, 6, 2] >>> 65 = [3, 1]`: `a` at 0, `b = [65]` at 3, top 4. -/
#guard (run natShrProg 100 "nat_shr" [0, 3, 3, 1]
  (Mem.ofWords [(POOL, #[0, 6, 2, 65, 0, 0, 0]), (CTL, #[4])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[0, 6, 2, 65, 3, 1, 0], #[6])
/- `a >>> 0 = a`; `[1] >>> 64 = 0`; `[1] >>> 2^64 = 0`. -/
#guard (run natShrProg 100 "nat_shr" [0, 2, 0, 0]
  (Mem.ofWords [(POOL, #[7, 9, 0, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) ==
  some ([2], #[7, 9, 7, 9], #[4])
#guard (run natShrProg 100 "nat_shr" [0, 1, 1, 1]
  (Mem.ofWords [(POOL, #[1, 64, 0]), (CTL, #[2])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[2])
#guard (run natShrProg 100 "nat_shr" [0, 1, 1, 2]
  (Mem.ofWords [(POOL, #[1, 0, 1, 0]), (CTL, #[3])])).toOption.map (fun (r, m) => (r, m.arr64 CTL)) ==
  some ([0], #[3])

section shrFn
variable (p : Prog)
  (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_shr" = some natShr)

set_option maxHeartbeats 0 in
include hpt hpn in
/-- `nat_shr` appends `a / 2^b` (`b` normalised), normalised, at the old top and moves the top
past it; nothing below the old top changes, and no other array but `CTL[0]`. -/
theorem natShr_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb)
    (hnb : Norm (vpool s₀.mem) ob.toNat lb.toNat) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_shr" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat / 2 ^ pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  sorry

end shrFn

end L.Arena
