module

import ConAgua.Census.Attr
public import ConAgua.Arena.NatAdd
import ConAgua.Arena.GrindAttr
import ConAgua.Arena.NatGrindAttr
import ConAgua.Arena.NatSub
import ConAgua.Front.Preserve
import ConAgua.L.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
import Std.WP.Triple.SpecLemmas

@[expose] public section

/-!
# `Nat.shiftLeft` on the limb pool: `nat_shl`

`nat_shl(oa, la, ob, lb)` is `a <<< b = a * 2^b` for two pool slices (con-ron's
`shift_left_nat`, `shl_onto`, `shl_bits_from`, `push_zeros`, `push_zeros_nat`,
`ron/nat.rs:313-403`). The amount `b` is a slice too; an amount of more than one limb, with
`a ≠ 0`, cannot fit any pool (con-ron runs out of memory pushing `u64::MAX` zero limbs), so it is
an `abort` here. Otherwise `k = b[0]`: `k >> 6` zero limbs, then `a` shifted by `k & 63` bits,
one pass with a carry, then `nat_trim`.

The bit shift is branch-free: limb `i` is `(x << s) | c` and the next carry
`(x >> 1) >> (63 - s)`, which is `x >> (64 - s)` for `s ≥ 1` and `0` for `s = 0`; con-ron
special-cases `s = 0` because `x >> 64` is not a legal `u64` shift. `shl_split` is the digit
equation `low + carry · 2^64 = x · 2^s + c`, the shape of `adc_split`.
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order

namespace L.Arena

/-! ## Word facts -/

/-- `2^s`, as a named function: `grind`'s ring solver sees it as one atom. -/
def sh (s : Nat) : Nat := 2 ^ s

theorem shl_lo (x b : Word) (hb : b.toNat < 64) :
    (x <<< b).toNat = x.toNat * 2 ^ b.toNat % 2 ^ 64 := by
  rw [UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (a := b.toNat) hb]

theorem shl_hi (x b : Word) (hb : b.toNat < 64) :
    ((x >>> 1) >>> (63 - b)).toNat = x.toNat * 2 ^ b.toNat / 2 ^ 64 := by
  have h63 : (63 - b).toNat = 63 - b.toNat := by grind
  rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftRight, h63]
  simp only [Nat.shiftRight_eq_div_pow, UInt64.toNat_one]
  rw [Nat.mod_eq_of_lt (by omega : 63 - b.toNat < 64), Nat.mod_eq_of_lt (by omega : 1 < 64)]
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_add]
  rw [show 1 + (63 - b.toNat) = 64 - b.toNat by omega]
  have : 2 ^ 64 = 2 ^ (64 - b.toNat) * 2 ^ b.toNat := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.mul_comm (2 ^ (64 - b.toNat)), ← Nat.div_div_eq_div_mul,
    Nat.mul_div_cancel _ (Nat.two_pow_pos _)]

theorem shl_split (x c b : Word) (hb : b.toNat < 64) (hc : c.toNat < 2 ^ b.toNat) :
    ((x <<< b) ||| c).toNat + ((x >>> 1) >>> (63 - b)).toNat * 2 ^ 64 =
      x.toNat * 2 ^ b.toNat + c.toNat := by
  rw [UInt64.toNat_or, shl_lo x b hb, shl_hi x b hb]
  have e : x.toNat * 2 ^ b.toNat % 2 ^ 64 = (x.toNat % 2 ^ (64 - b.toNat)) <<< b.toNat := by
    rw [Nat.shiftLeft_eq]
    have : 2 ^ 64 = 2 ^ (64 - b.toNat) * 2 ^ b.toNat := by rw [← Nat.pow_add]; congr 1; omega
    rw [this, Nat.mul_mod_mul_right]
  rw [e, ← Nat.shiftLeft_add_eq_or_of_lt hc, ← e]
  have := Nat.mod_add_div (x.toNat * 2 ^ b.toNat) (2 ^ 64)
  rw [Nat.mul_comm (x.toNat * 2 ^ b.toNat / 2 ^ 64)]
  omega

theorem shl_hi_lt (x b : Word) (hb : b.toNat < 64) :
    ((x >>> 1) >>> (63 - b)).toNat < 2 ^ b.toNat := by
  rw [shl_hi x b hb]
  apply Nat.div_lt_of_lt_mul
  have := x.toNat_lt
  have : 2 ^ 64 * 2 ^ b.toNat = 2 ^ (64 + b.toNat) := by rw [Nat.pow_add]
  calc x.toNat * 2 ^ b.toNat < 2 ^ 64 * 2 ^ b.toNat := Nat.mul_lt_mul_of_pos_right (by omega) (Nat.two_pow_pos _)

/-- The digit equation of one limb of the shift, over `sh`, as `grind` uses it. -/
theorem shl_split' (x c b : Word) (hb : b.toNat < 64) (hc : c.toNat < sh b.toNat) :
    ((x <<< b) ||| c).toNat + ((x >>> 1) >>> (63 - b)).toNat * 2 ^ 64 =
      x.toNat * sh b.toNat + c.toNat := shl_split x c b hb hc
grind_pattern [arena_grind] shl_split' => (x <<< b) ||| c

theorem shl_hi_lt' (x b : Word) (hb : b.toNat < 64) :
    ((x >>> 1) >>> (63 - b)).toNat < sh b.toNat := shl_hi_lt x b hb
grind_pattern [arena_grind] shl_hi_lt' => (x >>> 1) >>> (63 - b)

theorem and63_lt (k : Word) : (k &&& 63).toNat < 64 := by
  rw [UInt64.toNat_and]; exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
grind_pattern [arena_grind] and63_lt => k &&& 63

@[arena_grind =] theorem sh_zero : sh 0 = 1 := rfl

theorem sh_pos (s : Nat) : 0 < sh s := Nat.two_pow_pos _
grind_pattern [arena_grind] sh_pos => sh s

/-- The amount `k` is `64 · (k >> 6) + (k & 63)`. -/
theorem shamt (k : Word) : 2 ^ k.toNat = sh (k &&& 63).toNat * wt (k >>> 6).toNat := by
  simp only [sh, wt, ← Nat.pow_add]
  congr 1
  rw [UInt64.toNat_and, UInt64.toNat_shiftRight]
  simp only [Nat.shiftRight_eq_div_pow, show (63 : Word).toNat = 2 ^ 6 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, show (6 : Word).toNat % 64 = 6 from rfl]
  have := Nat.mod_add_div k.toNat (2 ^ 6)
  omega
grind_pattern [arena_grind] shamt => 2 ^ k.toNat

/-- A one-limb slice is its limb. -/
theorem pv_one (p : Array Word) (o : Nat) (h : o < p.size) : pv p o 1 = p[o].toNat := by
  simp [pv, h, wt]
grind_pattern [natop_grind] pv_one => pv p o 1, p[o]

/-! ## `nat_shl(oa, la, ob, lb)` -/

def shlZero : Stmt := lblk (oa, la, ob, lb, top, n, w, b, i, x, c, pt, pb) {
  while i < w {
    POOL⟨pt⟩[pb + i] := 0;
    i += 1
  }
}

def shlLoop : Stmt := lblk (oa, la, ob, lb, top, n, w, b, i, x, c, pt, pb) {
  while i < la {
    x := POOL⦃oa + i⦄;
    POOL⟨pt⟩[pb + (w + i)] := (x << b) | c;
    c := (x >> 1) >> (63 - b);
    i += 1
  }
}

/-- con-ron: ConRon/Arena/Core.lean:994-1035 ConRon.Arena.natOpResult -/
@[l_impl ConRon.Arena.natOpResult]
def natShl : FunDecl := lfn (oa, la, ob, lb) locals (top, n, w, b, i, x, c, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if la != 0 {
    if 1 < lb { abort };
    if lb == 1 { w := POOL⦃ob⦄ };
    b := w & 63;
    w := w >> 6;
    if len(POOL⟨pt⟩) - pb <= la { abort };
    if len(POOL⟨pt⟩) - pb - la - 1 < w { abort };
    ⟪shlZero⟫;
    i := 0;
    ⟪shlLoop⟫;
    POOL⟨pt⟩[pb + (w + la)] := c;
    n := call nat_trim(top, w + la + 1)
  };
  CTL.u64[0] := top + n;
  return n
}

/-- The pool functions with `nat_shl`. -/
def natShlProg : Prog := natProg ++ [("nat_shl", natShl)]

/- `[3, 1] <<< 65 = [0, 6, 2]`: `a` at 0 (2 limbs), `b = [65]` at 2, top 3. -/
#guard (run natShlProg 100 "nat_shl" [0, 2, 2, 1]
  { words := #[#[3, 1, 65, 0, 0, 0, 0], #[3]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([3], #[#[3, 1, 65, 0, 6, 2, 0], #[6]])
/- `2^63 <<< 1 = 2^64`; `a <<< 0 = a`; `0 <<< 2^64 = 0` (no abort). -/
#guard (run natShlProg 100 "nat_shl" [0, 1, 1, 1]
  { words := #[#[0x8000000000000000, 1, 0, 0, 0], #[2]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([2], #[#[0x8000000000000000, 1, 0, 1, 0], #[4]])
#guard (run natShlProg 100 "nat_shl" [0, 1, 1, 0]
  { words := #[#[7, 0, 0], #[1]] }).toOption.map (fun (r, m) => (r, m.words)) ==
  some ([1], #[#[7, 7, 0], #[2]])
#guard (run natShlProg 100 "nat_shl" [0, 0, 0, 2]
  { words := #[#[0, 1, 0], #[2]] }).toOption.map (·.1) == some [0]

section shl
variable (p : Prog) (Pg : Array Word) (C : Nat)

/-- What both loops of `nat_shl` keep: the pool agrees with the entry pool below `top`, `a` lies
below `top`, the `w + la + 1` result limbs fit above it, and the bit shift is below `64`. -/
def ShlBase (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  POOL < s.mem.words.size ∧ C < 2 ^ 63 ∧ Pg.size = 2 ^ 41 ∧ pcap s.mem = C ∧
  Agree (vpool s.mem) Pg (s.loc 4).toNat ∧
  (s.loc 4).toNat + (s.loc 6).toNat + (s.loc 1).toNat + 1 ≤ C ∧
  s.loc 11 = s.loc 4 >>> 40 ∧ s.loc 12 = s.loc 4 &&& 1099511627775 ∧
  (s.loc 12).toNat + (s.loc 6).toNat + (s.loc 1).toNat + 1 ≤ (s.mem.arr64 (tierA 0 (s.loc 11))).size ∧
  (s.mem.arr64 (tierA 0 (s.loc 11))).size ≤ 2 ^ 40 ∧ (s.loc 11).toNat ≤ 1 ∧ (s.loc 4).toNat < 2 ^ 41 ∧
  (s.loc 0).toNat + (s.loc 1).toNat ≤ (s.loc 4).toNat ∧ (s.loc 7).toNat < 64

def ShlZeroInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  ShlBase Pg C s ∧ (s.loc 8).toNat ≤ (s.loc 6).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat (s.loc 8).toNat = 0

/-- Limb `i` of `a`: the result up to limb `w + i`, plus the carry, is `a[0..i) · 2^s · wt w`. -/
def ShlInv (Pg : Array Word) (C : Nat) (s : St) : Prop :=
  ShlBase Pg C s ∧ (s.loc 8).toNat ≤ (s.loc 1).toNat ∧ (s.loc 10).toNat < sh (s.loc 7).toNat ∧
  pv (vpool s.mem) (s.loc 4).toNat ((s.loc 6).toNat + (s.loc 8).toNat) +
      (s.loc 10).toNat * (wt (s.loc 6).toNat * wt (s.loc 8).toNat) =
    pv Pg (s.loc 0).toNat (s.loc 8).toNat * sh (s.loc 7).toNat * wt (s.loc 6).toNat

def ShlZeroPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 0 = s₀.loc 0 ∧ s'.loc 1 = s₀.loc 1 ∧ s'.loc 2 = s₀.loc 2 ∧ s'.loc 3 = s₀.loc 3 ∧
  s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 6 = s₀.loc 6 ∧ s'.loc 7 = s₀.loc 7 ∧
  s'.loc 10 = s₀.loc 10 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat (s₀.loc 6).toNat = 0

def ShlPost (Pg : Array Word) (C : Nat) (s₀ : St) (r : Sig) (s' : St) : Prop :=
  r = .normal ∧ PFrame s₀.mem s'.mem ∧
  pcap s'.mem = C ∧ Agree (vpool s'.mem) Pg (s₀.loc 4).toNat ∧
  s'.loc 1 = s₀.loc 1 ∧ s'.loc 4 = s₀.loc 4 ∧ s'.loc 5 = s₀.loc 5 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧ s'.loc 6 = s₀.loc 6 ∧
  s'.loc 7 = s₀.loc 7 ∧ s'.loc 11 = s₀.loc 11 ∧ s'.loc 12 = s₀.loc 12 ∧
  (s'.loc 10).toNat < sh (s₀.loc 7).toNat ∧
  pv (vpool s'.mem) (s₀.loc 4).toNat ((s₀.loc 6).toNat + (s₀.loc 1).toNat) +
      (s'.loc 10).toNat * (wt (s₀.loc 6).toNat * wt (s₀.loc 1).toNat) =
    pv Pg (s₀.loc 0).toNat (s₀.loc 1).toNat * sh (s₀.loc 7).toNat * wt (s₀.loc 6).toNat

set_option maxHeartbeats 2000000 in
theorem shlZero_spec (n : Nat) (s₀ : St) (h : ShlZeroInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n shlZero ⦃fun r s' => ShlZeroPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [ShlZeroInv, ShlBase, ShlZeroPost] at h ⊢
    rw [exec, step_while (w := shlZero) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, setLoc, setLocs, st64, ih] <;>
      finish [ShlZeroInv, ShlBase, ShlZeroPost]

theorem shlZero_step_spec (n : Nat) (s₀ : St) (h : ShlZeroInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) shlZero ⦃fun r s' => ShlZeroPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (shlZero_spec p Pg C (n + 1) s₀ h)

/-- One step of the shift loop, in the shape of `shlLoop_spec`'s arithmetic goal (applied, not
E-matched: `grind` alone takes minutes here, chaining `pv_succ`/`pv_set_succ`/`wt_*` instances). -/
theorem shl_step_goal (m : Mem) (Pg : Array Word) (T T11 T12 o w i b c : Word)
    (h11 : T11 = T >>> 40) (h12 : T12 = T &&& 1099511627775)
    (hT : T.toNat < 2 ^ 41) (hs : (m.arr64 (tierA 0 T11)).size ≤ 2 ^ 40)
    (hst : (T12 + (w + i)).toNat < (m.arr64 (tierA 0 T11)).size)
    (hk : T12.toNat + w.toNat + i.toNat < 2 ^ 40)
    (hag : Agree (vpool m) Pg T.toNat) (hoi : o.toNat + i.toNat < T.toNat)
    (hwi : T.toNat + w.toNat + i.toNat < 2 ^ 41) (hi1 : i.toNat + 1 < 2 ^ 64)
    (hPg : Pg.size = 2 ^ 41) (hb : b.toNat < 64) (hc : c.toNat < sh b.toNat)
    (ih : pv (vpool m) T.toNat (w.toNat + i.toNat) + c.toNat * (wt w.toNat * wt i.toNat) =
      pv Pg o.toNat i.toNat * sh b.toNat * wt w.toNat)
    (hld : ((o + i) &&& 1099511627775).toNat < (m.arr64 (tierA 0 ((o + i) >>> 40))).size) :
    pv (vpool (m.set64 (tierA 0 T11) (T12 + (w + i))
        ((m.arr64 (tierA 0 ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat] <<< b ||| c)))
        T.toNat (w.toNat + (i + 1).toNat) +
      ((m.arr64 (tierA 0 ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat] >>> 1 >>> (63 - b)).toNat *
        (wt w.toNat * wt (i + 1).toNat) =
    pv Pg o.toNat (i + 1).toNat * sh b.toNat * wt w.toNat := by
  subst h11 h12
  have hwi' : (w + i).toNat = w.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hi' : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hoi' : (o + i).toNat = o.toNat + i.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hTwi : (T + (w + i)).toNat = T.toNat + (w.toNat + i.toNat) := by
    rw [UInt64.toNat_add, hwi']; exact Nat.mod_eq_of_lt (by omega)
  have hvs := vpool_size m
  have ex : (m.arr64 (tierA 0 ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat] = Pg[o.toNat + i.toNat] := by
    rw [vpool_ld m (o + i) hld (by omega)]
    simp only [hoi']
    exact Agree.get _ _ _ _ hag hoi (by omega) (by omega)
  rw [ex, vpool_stidx m T (w + i) _ hT hst hs (by omega), hTwi, hi']
  have hsp := shl_split' Pg[o.toNat + i.toNat] c b hb hc
  rw [pv_set_succ (vpool m) T.toNat (w.toNat + i.toNat) (w.toNat + (i.toNat + 1)) _ _ (by omega) rfl
    (by omega), pv_succ Pg o.toNat i.toNat (i.toNat + 1) (o.toNat + i.toNat) rfl rfl (by omega),
    wt_add w.toNat i.toNat (w.toNat + i.toNat) rfl, wt_succ i.toNat (i.toNat + 1) rfl]
  generalize pv (vpool m) T.toNat (w.toNat + i.toNat) = A at *
  generalize pv Pg o.toNat i.toNat = B at *
  generalize wt w.toNat = W at *
  generalize wt i.toNat = I at *
  generalize sh b.toNat = S at *
  grind

set_option maxHeartbeats 2000000 in
theorem shlLoop_spec (n : Nat) (s₀ : St) (h : ShlInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ exec p n shlLoop ⦃fun r s' => ShlPost Pg C s₀ r s'; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    simp only [ShlInv, ShlBase, ShlPost] at h ⊢
    rw [exec, step_while (w := shlLoop) rfl]
    -- `nat_mul`'s column-loop recipe (DESIGN.md, arena "How automatic"): the step is a
    -- multiply-accumulate identity that `grind` proves only without `ih` and the frame
    vcgen [step, evalE, evalC, setLoc, setLocs, ld64, st64, ih]
    all_goals clear ih
    all_goals (try simp only [ShlInv, ShlBase, ShlPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc, BinOp.eval, Cmp.eval, reduceIte, Nat.reduceEqDiff] at *)
    all_goals (try and_intros)
    all_goals first
      | (with_reducible apply shl_step_goal <;> grind)
      | grind (splits := 40) [arena_grind, lang_grind]

theorem shlLoop_step_spec (n : Nat) (s₀ : St) (h : ShlInv Pg C s₀) :
    ⦃fun s => s = s₀⦄ step p (exec p n) shlLoop ⦃fun r s' => ShlPost Pg C s₀ r s'; ⊤⦄ :=
  Triple.step_exec (shlLoop_spec p Pg C (n + 1) s₀ h)

end shl

/-- The value `nat_shl` returns, in the shape of `natShl_spec`'s goal: the loop's digit equation
(times `2^k = sh s * wt w`), the last carry stored at `top + (w + la)`, `nat_trim`, and the store
of the new top into `CTL`. -/
theorem shl_result_goal (m m0 : Mem) (T11 T12 w L c r top v oa la ob lb : Word)
    (h11 : T11 = top >>> 40) (h12 : T12 = top &&& 1099511627775)
    (hT : top.toNat < 2 ^ 41) (hs : (m.arr64 (tierA 0 T11)).size ≤ 2 ^ 40)
    (hst : (T12 + (w + L)).toNat < (m.arr64 (tierA 0 T11)).size)
    (hk : T12.toNat + w.toNat + L.toNat < 2 ^ 40)
    (hwl : top.toNat + w.toNat + L.toNat < 2 ^ 41) (hL : L = la)
    (htrim : pv (vpool (m.set64 (tierA 0 T11) (T12 + (w + L)) c)) top.toNat r.toNat =
      pv (vpool (m.set64 (tierA 0 T11) (T12 + (w + L)) c)) top.toNat (w + L + 1).toNat)
    (ih : pv (vpool m) top.toNat (w.toNat + L.toNat) + c.toNat * (wt w.toNat * wt L.toNat) =
      pv (vpool m0) oa.toNat la.toNat * 2 ^ pv (vpool m0) ob.toNat lb.toNat) :
    pv (vpool ((m.set64 (tierA 0 T11) (T12 + (w + L)) c).set64 1 0 v)) top.toNat r.toNat =
      pv (vpool m0) oa.toNat la.toNat * 2 ^ pv (vpool m0) ob.toNat lb.toNat := by
  subst h11 h12 hL
  have hwl' : (w + L).toNat = w.toNat + L.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hwl1 : (w + L + 1).toNat = w.toNat + L.toNat + 1 := by
    rw [UInt64.toNat_add, hwl', UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have hTwl : (top + (w + L)).toNat = top.toNat + (w.toNat + L.toNat) := by
    rw [UInt64.toNat_add, hwl']; exact Nat.mod_eq_of_lt (by omega)
  have hvs := vpool_size m
  rw [vpool_set64_ne _ 1 0 v (by decide), htrim, hwl1,
    vpool_stidx m top (w + L) c hT hst hs (by omega), hTwl,
    pv_set_succ (vpool m) top.toNat (w.toNat + L.toNat) (w.toNat + L.toNat + 1) _ _ rfl rfl (by omega),
    wt_add w.toNat L.toNat (w.toNat + L.toNat) rfl]
  generalize pv (vpool m) top.toNat (w.toNat + L.toNat) = A at *
  generalize pv (vpool m0) oa.toNat L.toNat = B at *
  generalize wt w.toNat = W at *
  generalize wt L.toNat = I at *
  generalize 2 ^ pv (vpool m0) ob.toNat lb.toNat = S at *
  grind

theorem shr6_zero : (0 : Word) >>> 6 = 0 := rfl
theorem and63_zero : (0 : Word) &&& 63 = 0 := rfl

section shlFn
variable (p : Prog) (hpt : p.lookup "nat_trim" = some natTrim) (hpn : p.lookup "nat_shl" = some natShl)

set_option maxHeartbeats 8000000 in
include hpt hpn in
/-- `nat_shl` appends `a * 2^b`, normalised, at the old top and moves the top past it; nothing
below the old top changes, and no other array but `CTL[0]`. -/
theorem natShl_spec (n : Nat) (s₀ : St) (oa la ob lb : Word) (hok : PoolOK s₀.mem)
    (ha : SliceOK s₀.mem oa la) (hb : SliceOK s₀.mem ob lb) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_shl" [oa, la, ob, lb]
    ⦃fun r s' => LocEq s' s₀ ∧ PFrame (s₀.mem.set64 CTL 0 (s₀.mem.top + r.headD 0)) s'.mem ∧
      pcap s'.mem = pcap s₀.mem ∧
      s₀.mem.top.toNat + (r.headD 0).toNat ≤ pcap s'.mem ∧
      Agree (vpool s'.mem) (vpool s₀.mem) s₀.mem.top.toNat ∧
      pv (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat =
        pv (vpool s₀.mem) oa.toNat la.toNat * 2 ^ pv (vpool s₀.mem) ob.toNat lb.toNat ∧
      Norm (vpool s'.mem) s₀.mem.top.toNat (r.headD 0).toNat ∧ Grows s₀.mem s'.mem; ⊤⦄ := by
  have hok₀ := hok
  have hsm := hok.small
  have h41 := hok.top41
  have hsz := hsm.tier (s₀.mem.top >>> 40)
  -- the `ptop0` disjunct of `PoolOK` is dead here, and `grind` splits on it in every goal
  obtain ⟨hok1, hok2, hok3, hok4, -, hok6⟩ := hok
  replace ha := ha.1
  replace hb := hb.1
  rw [invoke_eq _ hpn]
  simp only [callFn, natShl]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
      shlZero_step_spec p (vpool s₀.mem) (pcap s₀.mem) n, shlLoop_step_spec p (vpool s₀.mem) (pcap s₀.mem) n,
      natTrim_spec p hpt n]
    all_goals (try simp only [ShlZeroInv, ShlInv, ShlBase, ShlZeroPost, ShlPost] at *)
    all_goals (try subst_vars)
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, St.setLocs_nil, St.setLocs_cons, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, BinOp.eval, Cmp.eval, reduceIte,
      Nat.reduceEqDiff, UInt64.toNat_zero] at *)
    -- One `grind` per goal (no `and_intros`: 218 goals re-preprocess the same context). The
    -- result's value goes through `shl_result_goal` (`grind` alone: minutes per goal).
    all_goals first
      | (with_reducible apply shl_result_goal
         all_goals (try simp only [shr6_zero, and63_zero, UInt64.toNat_zero,
           pv_zero] at *)
         all_goals grind (splits := 40) [arena_grind, lang_grind, natop_grind])
      | grind (splits := 40) [arena_grind, lang_grind, natop_grind]

end shlFn

end L.Arena
