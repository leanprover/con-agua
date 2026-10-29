module

meta import ConAgua.L.Semantics
public import ConAgua.Arena.Pool
import ConAgua.Arena.GrindAttr
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

/-!
# Cons-table words: reads, the home slot, the slot base, variable shifts (lane slotgrow)

The word-level vocabulary of the cons tables (`ConsLib.lean`): `rdW` (a word, `0` past the end),
`homeW` (con-ron's `home_index`: the multiply-xor finaliser, then Lemire's range reduction), the
scratch tier's slot base `CTL[62]` (`SCB`, `baseW`, `slotRd`, `slotV`), the initial slot count
`SN0`, and `shiftS` (a block spliced into a function with its variables moved past the
function's own). The slot layout and the growth are `ConsLib.lean`'s; their models are
`SlotGrowSpec.lean`'s.
-/

set_option experimental.vcgen true

namespace L.Arena

/-- FNV-1a offset basis and prime (con-ron's `nat::hash64`). -/
def fnvBasis : Word := 0xcbf29ce484222325
def fnvPrime : Word := 0x100000001b3
/-- The multiply-xor finaliser of con-ron's `home_index` (`ron/hashmap2.rs`). -/
def golden : Word := 0x9e3779b97f4a7c15

/-! ## Words and slots -/

/-- A word of `a`, `0` past its end. -/
def rdW (a : Array Word) (x : Word) : Word := a[x.toNat]?.getD 0

theorem rdW_eq (a : Array Word) (x : Word) (k : Nat) (hk : k = x.toNat) (h : k < a.size) :
    rdW a x = a[k] := by subst hk; simp [rdW, h]
grind_pattern [arena_grind] rdW_eq => rdW a x, a[k]

/-- The home slot of hash `h` among `n`: con-ron's multiply-xor finaliser, then the high word
of the product with `n` (Lemire's range reduction) in place of the power-of-two mask. -/
def homeW (h n : Word) : Word :=
  UInt64.ofNat (((h * golden) ^^^ ((h * golden) >>> 32)).toNat * n.toNat / 2 ^ 64)

/-- The `CTL` word of the scratch tier's **slot base** `B` (`scratch_reset` adds `2^32`). A slot of
tier `t` holds `B t + i + 1` for node `i`, with `B 0 = 0` and `B 1 = CTL[62]`; a slot word at or
below the base is free. So the scratch tier is emptied by raising its base: every old slot falls
at or below the new base, and no slot is zeroed. -/
abbrev SCB : Word := 62

/-- The slot base of tier `t` (`t ≤ 1`): `CTL[62] * t`. -/
def baseW (m : Mem) (t : Word) : Word := rdW (m.arr64 CTL) SCB * t

/-- A slot word `v` against the base `b`: `0` (free) at or below `b`, else `i + 1`. -/
def slotRd (v b : Word) : Word := if v ≤ b then 0 else v - b

/-- Slot word `k` of `sl` against the base `b`. -/
def slotV (sl : Array Word) (b k : Word) : Word := slotRd (rdW sl k) b

/-- The mark of a slot waiting to be re-inserted by the in-place growth (`ConsLib.lean`'s
`kgrowB`): bit 63 of its value word (a live value word, `B t + i + 1`, is below `2^63`). -/
def MARK : Word := 9223372036854775808

/-- The initial slot count of a tier (its count word `0`). -/
def SN0 : Word := 8

/-- **The slot arrays' minimum length** (`ConsLib.lean`'s layout): the two initial tables of `SN0`
slots (two words each) on their sides of the middle, tier 0's from word 4 (`[4, 20)` below
`len / 2`, `[len - 16, len)` from it). The entry stub checks it (`capCond`), the relation needs it
(`consR_init`), every test memory below uses it. -/
def consMinWords : Nat := 18

/-- The slot arrays of the `#guard` test memories that intern a few nodes per tier (no growth). -/
def consTestWords : Nat := 2 * consMinWords

/-- The slot arrays of the test memories whose tier 0 grows once (to `2 SN0` slots at offset
`8 SN0`, ending at word `4 + 12 SN0` below the middle). -/
def consGrowWords : Nat := 2 + 12 * 8

/-! ## Tier arrays

Tier `t` of a store's array `a` is the word array `tierA a t` (`↑a`, or `tier1 a`): distinct
source arrays have distinct tiers, and the two tiers of one array differ. -/

/-- For `t ≤ 1`, tier `t` of `a` is `↑a` or `tier1 a` as `t` is `0` or `1`. -/
theorem tierA_of_le (a : Nat) (t : Word) (ht : t ≤ 1) :
    tierA a t = if t = 0 then (a : TieredArray) else tier1 a := by
  have : t.toNat ≤ 1 := ht
  rcases (show t.toNat = 0 ∨ t.toNat = 1 by omega) with h | h
  · rw [UInt64.toNat_inj.mp (h.trans UInt64.toNat_zero.symm)]; rfl
  · rw [UInt64.toNat_inj.mp (h.trans UInt64.toNat_one.symm)]; rfl

@[simp] theorem tierA_zero (a : Nat) : tierA a 0 = a := rfl
@[simp] theorem tierA_one (a : Nat) : tierA a 1 = tier1 a := rfl

theorem tierA_and_one (a : Nat) (t : Word) : tierA a (t &&& 1) = tierA a t := by
  simp only [tierA, UInt64.and_assoc, UInt64.and_self]

theorem and_one_le (t : Word) : (t &&& 1).toNat ≤ 1 := by
  rw [UInt64.toNat_and]; exact Nat.le_trans Nat.and_le_right (by simp)

theorem tierA_inj {a b : Nat} {t u : Word} (ht : t ≤ 1) (hu : u ≤ 1) :
    tierA a t = tierA b u ↔ a = b ∧ t = u := by
  have h01 : ∀ x : Word, x ≤ 1 → x = 0 ∨ x = 1 := fun x hx => by
    have : x.toNat ≤ 1 := hx
    rcases (show x.toNat = 0 ∨ x.toNat = 1 by omega) with e | e
    · exact .inl (UInt64.toNat_inj.mp (e.trans UInt64.toNat_zero.symm))
    · exact .inr (UInt64.toNat_inj.mp (e.trans UInt64.toNat_one.symm))
  rcases h01 t ht with rfl | rfl <;> rcases h01 u hu with rfl | rfl <;> simp

/-- Arrays in any tiers differ when the source arrays do. -/
theorem tierA_ne {a b : Nat} (h : a ≠ b) (t u : Word) : tierA a t ≠ tierA b u :=
  tierA_ne_tierA h t u

/-- A plain array is neither tier of another array. -/
theorem ne_tierA {a b : Nat} (h : a ≠ b) (t : Word) : (a : TieredArray) ≠ tierA b t := by
  simpa using tierA_ne h 0 t

/-- The two tiers of one array differ. -/
theorem tierA_ne_tier (a : Nat) {t u : Word} (ht : t ≤ 1) (hu : u ≤ 1) (h : t ≠ u) :
    tierA a t ≠ tierA a u := fun e => h ((tierA_inj ht hu).1 e).2

/-! ## Shifting local variables

A block written once with its variables first (a table's key hash, `ConsSch.ihash`) is spliced
into a function with its variables moved past the function's own (`shiftS o`). -/

/-- Expression `e` with every local variable index raised by `o`. -/
def shiftE (o : Nat) : Expr → Expr
  | .var x => .var (x + o)
  | .bin op a b => .bin op (shiftE o a) (shiftE o b)
  | .ld8 a i => .ld8 a (shiftE o i)
  | .ld64 a i => .ld64 a (shiftE o i)
  | .cmpw c a b => .cmpw c (shiftE o a) (shiftE o b)
  | .ldc d i => .ldc d (shiftE o i)
  | .ld64t a t i => .ld64t a (shiftE o t) (shiftE o i)
  | .len64t a t => .len64t a (shiftE o t)
  | .ld8x8 b i => .ld8x8 b (shiftE o i)
  | .ld32t a t i => .ld32t a (shiftE o t) (shiftE o i)
  | e => e

/-- A block operand with its tier expression renamed. -/
def shiftW (o : Nat) : WArr → WArr
  | .plain a => .plain a
  | .tier a t => .tier a (shiftE o t)

/-- Condition `c` with every local variable index raised by `o`. -/
def shiftC (o : Nat) : Cond → Cond
  | .cmp c a b => .cmp c (shiftE o a) (shiftE o b)
  | .and p q => .and (shiftC o p) (shiftC o q)
  | .or p q => .or (shiftC o p) (shiftC o q)
  | .not p => .not (shiftC o p)

/-- Statement `s` with every local variable index raised by `o`. -/
def shiftS (o : Nat) : Stmt → Stmt
  | .set x e => .set (x + o) (shiftE o e)
  | .st8 a i e => .st8 a (shiftE o i) (shiftE o e)
  | .st64 a i e => .st64 a (shiftE o i) (shiftE o e)
  | .seq s t => .seq (shiftS o s) (shiftS o t)
  | .ite c s t => .ite (shiftC o c) (shiftS o s) (shiftS o t)
  | .while c s => .while (shiftC o c) (shiftS o s)
  | .ret es => .ret (es.map (shiftE o))
  | .call xs f args => .call (xs.map (· + o)) f (args.map (shiftE o))
  | .gset g e => .gset g (shiftE o e)
  | .st64t a t i e => .st64t a (shiftE o t) (shiftE o i) (shiftE o e)
  | .copy64 d di s si n => .copy64 (shiftW o d) (shiftE o di) (shiftW o s) (shiftE o si) (shiftE o n)
  | .copy8w d di s si n => .copy8w (shiftW o d) (shiftE o di) s (shiftE o si) (shiftE o n)
  | .scan8 x s i e c => .scan8 (x + o) s (shiftE o i) (shiftE o e) c
  | .st32t a t i e => .st32t a (shiftE o t) (shiftE o i) (shiftE o e)
  | .abort e => .abort (shiftE o e)
  | s => s

end L.Arena
