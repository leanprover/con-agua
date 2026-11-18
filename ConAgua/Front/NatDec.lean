module

public import ConAgua.Arena.SlotGrow
public import ConAgua.Arena.NatMul
public import ConAgua.Front.Fields
public import Std.Data.DTreeMap.Internal.Operations
import Std.WP.Triple.SpecLemmas
public import ConAgua.Arena.CallF
import ConAgua.Arena.GrindAttr
import ConAgua.Census.Attr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
meta import ConAgua.Arena.SlotGrow
meta import ConAgua.Arena.NatMul
meta import ConAgua.Front.Fields
meta import Std.Data.DTreeMap.Internal.Operations
meta import Std.WP.Triple.SpecLemmas
meta import ConAgua.Arena.GrindAttr
meta import ConAgua.Census.Attr
meta import ConAgua.L.GrindAttr
meta import Std.Tactic.BVDecide.Normalize.BitVec
meta import Std.Tactic.BVDecide.Normalize.Prop
meta import Std.WP.Tactic

@[expose] public section

/-!
# Decimal `Nat` literals into the limb pool: `nat_dec(c, d)`

con-ron's `frontend/nat_decimal.rs` (`from_decimal`, `from_decimal_go`, `mul_add_small`): the
digits `[c, d)` of the input are read nineteen at a time (`10^19 < 2^64`), and each chunk is
folded into the limbs by one multiply-add pass, `limbs := limbs * 10^k + chunk`. In L the limbs
are a slice at the pool top that grows in place:

* `dec_chunk(i, k)`: the value `ch` of the `k ≤ 19` digits at `i`, and `pw = 10^k`.
* `nat_mad(o, n, w, y)`: the slice `(o, n)` becomes `(o, n) * w + y` in place, the carry out is
  returned (Rust's `u128` accumulator as the low word `x * w + y` and the high word
  `mulhi(x, w) + u64(lo < y)`). This is the helper lane `nat` has no copy of yet
  (`mul_add_small`); it belongs with `NatMul.lean`.
* `nat_dec(c, d)`: the chunk loop; a non-zero carry is one more limb at the end (abort when the
  pool is full); then the top moves past the slice, which is returned as `(top, n)`.

The limbs are normalised throughout (no leading zero limb is ever written: the carry limb is
non-zero, and a product of a normalised slice by `10^k ≥ 1` keeps its top limb non-zero).

Each L function's spec is an equation about a named model (`chunkN`, `madW`, `decW`); the
facts about the models are proved by hand below them, and `natDec_spec` relates the result to
con-leche's `readNatAt` on a literal the scanner accepted (`NatValR`).
-/

set_option experimental.vcgen true

open Std.WP
open scoped Lean.Order
open L.Arena

namespace L.Front

open L.Scan.Utf8 (byteW)

/-- The longest literal `nat_dec` reads by the chunk loop alone (measured, docs/design/bigdec.md). -/
abbrev decBase : Word := 4864

/-! ## `dec_chunk(i, k)` -/

def chunkLoop : Stmt := lblk (i, k, ch, pw, j) {
  for j < k {
    ch := ch * 10 + ((IN.u8[i + j] - 48) & 255);
    pw := pw * 10
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:466-478 ConLeche.Frontend.readNat64 -/
@[no_expose] def decChunk : FunDecl := lfn (i, k) locals (ch, pw, j) {
  pw := 1;
  ⟪chunkLoop⟫;
  return (ch, pw)
}

/-- The model of the chunk loop: `(ch, pw)` after digits `j ‥ k` of the chunk at `i`. -/
def chunkN (b : Array UInt8) (i k j ch pw : Word) : Word × Word :=
  if j < k then chunkN b i k (j + 1) (ch * 10 + ((byteW b (i + j) - 48) &&& 255)) (pw * 10)
  else (ch, pw)
termination_by k.toNat - j.toNat
decreasing_by
  have : j.toNat < k.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹j < k›
  have := k.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

section
variable (b : Array UInt8) (i k j ch pw : Word)
theorem chunkN_stop (h : ¬ j < k) : chunkN b i k j ch pw = (ch, pw) := by
  rw [chunkN, ite_eq_right h]
theorem chunkN_step (h : j < k) : chunkN b i k j ch pw =
    chunkN b i k (j + 1) (ch * 10 + ((byteW b (i + j) - 48) &&& 255)) (pw * 10) := by
  rw [chunkN, ite_eq_left h]
end
grind_pattern [lang_grind] chunkN_stop => chunkN b i k j ch pw
grind_pattern [lang_grind] chunkN_step => chunkN b i k j ch pw, b[(i + j).toNat]

/-! ## `nat_mad(o, n, w, y)` -/

def madLoop : Stmt := lblk (o, n, w, y, i, x, lo, pt, pb) {
  for i < n {
    x := POOL⦃o + i⦄;
    lo := x * w + y;
    y := mulhi(x, w) + u64(lo < y);
    POOL⟨pt⟩[pb + i] := lo
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:466-478 ConLeche.Frontend.readNat64 -/
@[no_expose] def natMad : FunDecl := lfn (o, n, w, y) locals (i, x, lo, pt, pb) {
  pt := ⦃o⦄.tier;
  pb := ⦃o⦄.idx;
  ⟪madLoop⟫;
  return y
}

/-- The high word of `x * w + y` (`mulhi` and the carry of the low addition). -/
def madHi (x w y : Word) : Word :=
  UInt64.ofNat (x.toNat * w.toNat / 2 ^ 64) + (if x * w + y < y then 1 else 0)

/-- The model of the multiply-add loop from limb `i` with carry `y`: the memory and the carry
(limb `i` read at the tagged address `o + i`, written at index `⦃o⦄.idx + i` of `o`'s tier). -/
def madW (m : Mem) (o n w y i : Word) : Mem × Word :=
  if i < n then
    madW (m.set64 (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + i) (prd m (o + i) * w + y)) o n w
      (madHi (prd m (o + i)) w y) (i + 1)
  else (m, y)
termination_by n.toNat - i.toNat
decreasing_by
  have : i.toNat < n.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹i < n›
  have := n.toNat_lt
  have : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  omega

section
variable (m m' : Mem) (o n w y y' i i' : Word)
theorem madW_stop (h : ¬ i < n) : madW m o n w y i = (m, y) := by
  rw [madW, ite_eq_right h]
theorem madW_step (k : Nat) (h : i < n) (hk : k = ((o + i) &&& 1099511627775).toNat)
    (hks : k < (m.arr64 (tierA POOL ((o + i) >>> 40))).size)
    (hi' : i' = i + 1)
    (hm' : m' = m.set64 (tierA POOL (o >>> 40)) ((o &&& 1099511627775) + i)
      ((m.arr64 (tierA POOL ((o + i) >>> 40)))[k] * w + y))
    (hy' : y' = UInt64.ofNat ((m.arr64 (tierA POOL ((o + i) >>> 40)))[k].toNat * w.toNat / 2 ^ 64) +
      (if (m.arr64 (tierA POOL ((o + i) >>> 40)))[k] * w + y < y then 1 else 0)) :
    madW m o n w y i = madW m' o n w y' i' := by
  subst hi' hm' hk
  have e : (m.arr64 (tierA POOL ((o + i) >>> 40)))[((o + i) &&& 1099511627775).toNat] = prd m (o + i) :=
    prd_ld m (o + i) hks
  rw [e] at hy' ⊢
  subst hy'
  rw [madW, ite_eq_left h]
  simp only [madHi]
end
grind_pattern [arena_grind] madW_stop => madW m o n w y i
grind_pattern [arena_grind] madW_step => madW m o n w y i, (m.arr64 (tierA POOL ((o + i) >>> 40)))[k],
  madW m' o n w y' i'

theorem madW_bytes (m : Mem) (o n w y i : Word) : (madW m o n w y i).1.bytes = m.bytes := by
  fun_induction madW m o n w y i with
  | case1 m y i h ih => rw [ih]; rfl
  | case2 m y i h => rfl

theorem madW_arr8 (m : Mem) (o n w y i : Word) (a : ArrId) :
    (madW m o n w y i).1.arr8 a = m.arr8 a := by
  simp only [Mem.arr8, madW_bytes]
grind_pattern [lang_grind] madW_arr8 => (madW m o n w y i).1.arr8 a

/-! ## `nat_dec(c, d)` -/

def decLoop : Stmt := lblk (c, d, top, n, i, k, ch, pw, cy, pt, pb) {
  while i < d {
    k := d - i;
    if 19 < k { k := 19 };
    (ch, pw) := call dec_chunk(i, k);
    cy := call nat_mad(top, n, pw, ch);
    if cy != 0 {
      if len(POOL⟨pt⟩) <= pb + n { abort };
      POOL⟨pt⟩[pb + n] := cy;
      n += 1
    };
    i += k
  }
}

/-- con-leche: ConLeche/Frontend/Scan/Fast.lean:466-478 ConLeche.Frontend.readNat64 -/
@[no_expose] def natDecChunks : FunDecl := lfn (c, d) locals (top, n, i, k, ch, pw, cy, pt, pb) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  i := c;
  ⟪decLoop⟫;
  CTL.u64[0] := top + n;
  return (top, n)
}

/-! ## Long literals: divide and conquer (`nat_dec_split`, `nat_dec_big`) -/

/-- `nat_dec_split(c, d, tbl, k)`: the value of the digits `[c, d)` appended at the pool top,
`(top, len)`. At most `decBase` digits: the chunk loop. Longer: with `dd = 19 · 2^t` the largest
with `4 dd ≤ len`, the high part `[c, d - dd)` times `10^dd` (the table's entry `t` at `tbl`, two
words `(address, length)` each; `t < k`) plus the low part `[d - dd, d)`, by `nat_mul` and
`nat_add`; the sum is copied down to the old top. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `frontend/nat_decimal.rs` `read_split`); the twin computes on `Nat`
@[no_expose] def natDecSplit : FunDecl :=
  lfn (c, d, tbl, k) locals (n, t, dd, m, top, oh, lh, ol, ll, po, pl, op, lp, os, ls, pt, pb) {
  n := d - c;
  if n <= ⟪decBase⟫ {
    (oh, lh) := call nat_dec_chunks(c, d);
    return (oh, lh)
  };
  dd := 19;
  while dd + dd <= n - dd - dd { dd := dd + dd; t += 1 };
  if k <= t { abort };
  m := d - dd;
  top := CTL.u64[0];
  (oh, lh) := call nat_dec_split(c, m, tbl, k);
  (ol, ll) := call nat_dec_split(m, d, tbl, k);
  po := POOL⦃tbl + t + t⦄;
  pl := POOL⦃tbl + t + t + 1⦄;
  op := CTL.u64[0];
  lp := call nat_mul(oh, lh, po, pl);
  os := CTL.u64[0];
  ls := call nat_add(op, lp, ol, ll);
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  copy!(POOL.u64⟨pt⟩, pb, POOL.u64⟨pt⟩, ⦃os⦄.idx, ls);
  CTL.u64[0] := top + ls;
  return (top, ls)
}

/-- `nat_dec_big(c, d)`: the power table `10^(19 · 2^t)` for every `t` with `4 · 19 · 2^t ≤ d - c`
(and `t = 0`), by squaring with `nat_mul`, then `nat_dec_split`; the result is copied down to
the old top. -/
-- con-ron: none — limb arithmetic of the bignum (con-ron `frontend/nat_decimal.rs` `power_table`); the twin computes on `Nat`
@[no_expose] def natDecBig : FunDecl := lfn (c, d) locals (top, pt, pb, n, k, dd, i, o, l, s, r) {
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  n := d - c;
  k := 1;
  dd := 19;
  while dd + dd <= n - dd - dd { dd := dd + dd; k += 1 };
  if len(POOL⟨pt⟩) < pb + k + k + 1 { abort };
  POOL⟨pt⟩[pb + k + k] := 10000000000000000000;
  POOL⟨pt⟩[pb] := top + k + k;
  POOL⟨pt⟩[pb + 1] := 1;
  CTL.u64[0] := top + k + k + 1;
  i := 1;
  while i < k {
    o := POOL⟨pt⟩[pb + i + i - 2];
    l := POOL⟨pt⟩[pb + i + i - 1];
    s := CTL.u64[0];
    r := call nat_mul(o, l, o, l);
    POOL⟨pt⟩[pb + i + i] := s;
    POOL⟨pt⟩[pb + i + i + 1] := r;
    i += 1
  };
  (o, l) := call nat_dec_split(c, d, top, k);
  copy!(POOL.u64⟨pt⟩, pb, POOL.u64⟨pt⟩, ⦃o⦄.idx, l);
  CTL.u64[0] := top + l;
  return (top, l)
}

/-- `nat_dec(c, d)`: at most `decBase` digits by the chunk loop, longer ones by
`nat_dec_big`.
con-leche: ConLeche/Frontend/Scan/Fast.lean:466-478 ConLeche.Frontend.readNat64 -/
-- con-leche: ConLeche/Frontend/Scan/Fast.lean:103-112 ConLeche.Frontend.readNat
@[no_expose, l_impl ConLeche.Frontend.readNat64 ConLeche.Frontend.readNat]
def natDec : FunDecl := lfn (c, d) locals (o, l) {
  if c < d && ⟪decBase⟫ < d - c {
    (o, l) := call nat_dec_big(c, d)
  } else {
    (o, l) := call nat_dec_chunks(c, d)
  };
  return (o, l)
}

/-- The chunk length at `i`: at most nineteen digits. -/
def decK (i d : Word) : Word := if 19 < d - i then 19 else d - i

theorem decK_pos (i d : Word) (h : i < d) : 0 < (decK i d).toNat ∧ (i + decK i d).toNat ≤ d.toNat ∧
    (i + decK i d).toNat = i.toNat + (decK i d).toNat ∧ (decK i d).toNat ≤ 19 := by
  have h1 := UInt64.lt_iff_toNat_lt.mp h
  have hs : (d - i).toNat = d.toNat - i.toNat := UInt64.toNat_sub_of_le _ _ (UInt64.le_of_lt h)
  have hd := d.toNat_lt
  unfold decK
  split
  · rename_i h19
    have := UInt64.lt_iff_toNat_lt.mp h19
    simp only [UInt64.reduceToNat] at this
    have e : (i + 19).toNat = i.toNat + 19 := by
      rw [UInt64.toNat_add]; simp only [UInt64.reduceToNat]; rw [Nat.mod_eq_of_lt (by omega)]
    simp only [UInt64.reduceToNat]; omega
  · rename_i h19
    have := UInt64.not_lt.mp h19
    have := UInt64.le_iff_toNat_le.mp this
    simp only [UInt64.reduceToNat] at this
    have e : (i + (d - i)).toNat = i.toNat + (d - i).toNat := by
      rw [UInt64.toNat_add, hs, Nat.mod_eq_of_lt (by omega)]
    rw [e, hs]; omega

/-- The model of the chunk loop of `nat_dec`, from position `i` with `n` limbs at `top`: the
memory and the length, `none` where the L code aborts (the pool is full). -/
def decW (b : Array UInt8) (m : Mem) (top n i d : Word) : Option (Mem × Word) :=
  if _h : i < d then
    if (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).2 ≠ 0 then
      if (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).1.len64
          (tierA POOL (top >>> 40)) ≤ (top &&& 1099511627775) + n then none
      else decW b ((madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).1.set64
        (tierA POOL (top >>> 40)) ((top &&& 1099511627775) + n) (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).2)
        top (n + 1) (i + decK i d) d
    else decW b (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).1
      top n (i + decK i d) d
  else some (m, n)
termination_by d.toNat - i.toNat
decreasing_by
  all_goals have := decK_pos i d _h; omega

section
variable (b : Array UInt8) (m : Mem) (top n i d : Word)
theorem decW_stop (h : ¬ i < d) : decW b m top n i d = some (m, n) := by
  rw [decW, dite_eq_right h]
theorem decW_step (h : i < d) : decW b m top n i d =
    if (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).2 ≠ 0 then
      if (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).1.len64
          (tierA POOL (top >>> 40)) ≤ (top &&& 1099511627775) + n then none
      else decW b ((madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).1.set64
        (tierA POOL (top >>> 40)) ((top &&& 1099511627775) + n) (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).2)
        top (n + 1) (i + decK i d) d
    else decW b (madW m top n (chunkN b i (decK i d) 0 0 1).2 (chunkN b i (decK i d) 0 0 1).1 0).1
      top n (i + decK i d) d := by
  rw [decW, dite_eq_left h]
end
grind_pattern [lang_grind] decW_stop => decW b m top n i d
grind_pattern [lang_grind] decW_step => decW b m top n i d

/-- After the loop: `(top, n)` and the memory with the top moved. -/
def finK (top : Word) : Option (Mem × Word) → Option (List Word × Mem)
  | some (m₁, n) => some ([top, n], m₁.set64 CTL 0 (top + n))
  | none => none

@[lang_grind =] theorem finK_none (top : Word) : finK top none = none := rfl
@[lang_grind =] theorem finK_some (top n : Word) (m₁ : Mem) :
    finK top (some (m₁, n)) = some ([top, n], m₁.set64 CTL 0 (top + n)) := rfl

/-- The model of `nat_dec_chunks(c, d)`: the result and the memory, `none` where it aborts. -/
def natChunksW (b : Array UInt8) (m : Mem) (c d : Word) : Option (List Word × Mem) :=
  if m.len64 (tierA POOL (rdW (m.arr64 CTL) 0 >>> 40)) < (rdW (m.arr64 CTL) 0 &&& 1099511627775) then none
  else finK (rdW (m.arr64 CTL) 0) (decW b m (rdW (m.arr64 CTL) 0) 0 c d)

/-- The functions of `nat_dec`, with the pool's `nat_mul` and `nat_add`, as one program. -/
def natDecProg : Prog := L.Arena.natMulProg ++ [("dec_chunk", decChunk), ("nat_mad", natMad),
  ("nat_dec_chunks", natDecChunks), ("nat_dec_split", natDecSplit), ("nat_dec_big", natDecBig),
  ("nat_dec", natDec)]

/-- **The model of `nat_dec(c, d)`**: the result and the memory, `none` where it aborts; a
long literal is `nat_dec_big`'s run in `natDecProg` (`callF`). -/
noncomputable def natDecW (b : Array UInt8) (m : Mem) (c d : Word) : Option (List Word × Mem) :=
  if c < d ∧ decBase < d - c then callF natDecProg "nat_dec_big" m [c, d] else natChunksW b m c d

/- `12345678901234567890123` (23 digits, two chunks) at pool top 1: limbs
`[4807115922877859019, 669]` at 1, the top moves to 3. -/
#guard (run natDecProg 1000 "nat_dec" [1, 24]
  ((Mem.ofWords [(POOL, #[7, 0, 0, 0]), (CTL, #[1])]).putBytes IN "x12345678901234567890123".toUTF8.data)).toOption.map
  (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL)) == some ([1, 2], #[7, 4807115922877859019, 669, 0], #[3])
/- `0` and `00` have no limbs; `7` one. -/
#guard (run natDecProg 1000 "nat_dec" [0, 2]
  ((Mem.ofWords [(POOL, #[0]), (CTL, #[0])]).putBytes IN "00".toUTF8.data)).toOption.map (·.1) == some [0, 0]
#guard (run natDecProg 1000 "nat_dec" [0, 1]
  ((Mem.ofWords [(POOL, #[0]), (CTL, #[0])]).putBytes IN "7".toUTF8.data)).toOption.map (fun (r, m) => (r, m.arr64 POOL, m.arr64 CTL))
  == some ([0, 1], #[7], #[1])
/- A full pool aborts. -/
#guard (run natDecProg 1000 "nat_dec" [0, 1]
  ((Mem.ofWords [(POOL, #[]), (CTL, #[0])]).putBytes IN "7".toUTF8.data)).toOption.isNone

/-! ## The specs -/

section specs
variable (p : Prog) (b : Array UInt8)
  (hpc : p.lookup "dec_chunk" = some decChunk) (hpm : p.lookup "nat_mad" = some natMad)
  (hpd : p.lookup "nat_dec_chunks" = some natDecChunks)

theorem chunkLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    exec p n chunkLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 2 = (chunkN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 4) (s₀.loc 2) (s₀.loc 3)).1 ∧
      s'.loc 3 = (chunkN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 4) (s₀.loc 2) (s₀.loc 3)).2; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := chunkLoop) rfl]
    sym only [lang_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, ld8, ih] <;> finish

theorem chunkLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b⦄
    step p (exec p n) chunkLoop
    ⦃fun r s' => s'.mem = s₀.mem ∧ r = .normal ∧
      s'.loc 2 = (chunkN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 4) (s₀.loc 2) (s₀.loc 3)).1 ∧
      s'.loc 3 = (chunkN b (s₀.loc 0) (s₀.loc 1) (s₀.loc 4) (s₀.loc 2) (s₀.loc 3)).2; ⊤⦄ :=
  Triple.step_exec (chunkLoop_spec p b (n + 1) s₀)

include hpc in
theorem decChunk_spec (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (i k : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "dec_chunk" [i, k]
    ⦃fun r s' => s' = s₀ ∧ r = [(chunkN b i k 0 0 1).1, (chunkN b i k 0 0 1).2]; ⊤⦄ := by
  rw [invoke_eq _ hpc]
  simp only [callFn, decChunk]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, chunkLoop_step_spec p b n] <;> finish

theorem madLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.loc 7 = s.loc 0 >>> 40 ∧ s.loc 8 = s.loc 0 &&& 1099511627775⦄
    exec p n madLoop
    ⦃fun r s' => r = .normal ∧
      s'.mem = (madW s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).1 ∧
      s'.loc 3 = (madW s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2; ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := madLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, ld64, st64, ih] <;> finish

theorem madLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.loc 7 = s.loc 0 >>> 40 ∧ s.loc 8 = s.loc 0 &&& 1099511627775⦄
    step p (exec p n) madLoop
    ⦃fun r s' => r = .normal ∧
      s'.mem = (madW s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).1 ∧
      s'.loc 3 = (madW s₀.mem (s₀.loc 0) (s₀.loc 1) (s₀.loc 2) (s₀.loc 3) (s₀.loc 4)).2; ⊤⦄ :=
  Triple.step_exec (madLoop_spec p (n + 1) s₀)

include hpm in
theorem natMad_spec (n : Nat) (s₀ : St) (o l w y : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_mad" [o, l, w, y]
    ⦃fun r s' => LocEq s' s₀ ∧ r = [(madW s₀.mem o l w y 0).2] ∧
      s'.mem = (madW s₀.mem o l w y 0).1; ⊤⦄ := by
  rw [invoke_eq _ hpm]
  simp only [callFn, natMad]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, madLoop_step_spec p n] <;> finish

attribute [local lang_grind] decK in
include hpc hpm in
theorem decLoop_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 9 = s.loc 2 >>> 40 ∧
      s.loc 10 = s.loc 2 &&& 1099511627775⦄
    exec p n decLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      decW b s₀.mem (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 1) = some (s'.mem, s'.loc 3); ⊤⦄ := by
  induction n generalizing s₀ with
  | zero => vcgen [exec] <;> grind
  | succ n ih =>
    rw [exec, step_while (w := decLoop) rfl]
    sym only [lang_grind, arena_grind] =>
      vcgen [step, evalE, evalC, evalArgs, setLoc, setLocs, st64, ih,
        decChunk_spec p b hpc n, natMad_spec p hpm n] <;> finish

include hpc hpm in
theorem decLoop_step_spec (n : Nat) (s₀ : St) :
    ⦃fun s => s = s₀ ∧ s.mem.arr8 IN = b ∧ s.loc 9 = s.loc 2 >>> 40 ∧
      s.loc 10 = s.loc 2 &&& 1099511627775⦄
    step p (exec p n) decLoop
    ⦃fun r s' => r = .normal ∧ s'.loc 2 = s₀.loc 2 ∧
      decW b s₀.mem (s₀.loc 2) (s₀.loc 3) (s₀.loc 4) (s₀.loc 1) = some (s'.mem, s'.loc 3); ⊤⦄ :=
  Triple.step_exec (decLoop_spec p b hpc hpm (n + 1) s₀)

include hpc hpm hpd in
/-- **`nat_dec(c, d)`'s model equation.** -/
theorem natDecChunks_specW (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_dec_chunks" [c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ natChunksW b s₀.mem c d = some (r, s'.mem); ⊤⦄ := by
  rw [invoke_eq _ hpd]
  simp only [callFn, natDecChunks]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, st64,
        decLoop_step_spec p b hpc hpm n] <;> finish [natChunksW, rdW]

include hpc hpm in
/-- **`nat_dec(c, d)`'s model equation.** -/
theorem natDec_specW (hpn : p.lookup "nat_dec" = some natDec) (n : Nat) (s₀ : St) (hm : s₀.mem.arr8 IN = b) (c d : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "nat_dec" [c, d]
    ⦃fun r s' => LocEq s' s₀ ∧ natDecW b s₀.mem c d = some (r, s'.mem); ⊤⦄ := by
  sorry

end specs

end L.Front
