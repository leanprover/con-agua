import ConAgua.Front.StateDR
import ConAgua.L.Blocks
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop
import Std.WP.Tactic
set_option linter.unusedSectionVars false

/-!
# The ROM: constant con-leche data as bytes, and the L readers

con-ron interns con-leche *values* (the pinned names, the basis blocks, the axiom shapes, the
`Nat`-operation pin sets: `internName`, `internExprGo`, `internCI`, …) into the store, at startup
(`internReservedPins`, `internAllPins`) and again inside some checks (`basisPinHit`, `andPinOk`,
the axiom pins). L has no such values: they are **bytes of the program's constant data** (`ldc`,
`rom.c8[i]`), one byte string `rom` for the whole program, and one generic interner per value
type reads them.

**The encoding** (`encName`, …) is a prefix serialisation in the twin's intern order: a node's
tag byte, then its children in the order the twin interns them, then its own payload. Numbers
are 8 bytes, little endian (`u64B`); a string is its UTF-8 length (8 bytes) and its bytes.

**No decoder.** A spec says: if `rom.drop pos = enc x ++ rest`, the L reader at `pos` interns
`x` the way the twin does and returns the position past `enc x`. The proof is by induction on
`x`; the ROM's contents enter only through that equation, which for concrete data is
`List.drop_append` on the definition of `rom` (`Prelude.lean`).

This file: the encoding, `rom_u64(i)` (a number), `rom_put(i, l)` (copy `l` bytes to the pool
top, as `str_put` does from the input), `rom_name(pos)` (refines `internName`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Rom

open L.Arena

/-! ## The encoding -/

/-- A number below `2^64` as 8 bytes, little endian. -/
def u64B (n : Nat) : List UInt8 :=
  [UInt8.ofNat n, UInt8.ofNat (n / 2 ^ 8), UInt8.ofNat (n / 2 ^ 16), UInt8.ofNat (n / 2 ^ 24),
   UInt8.ofNat (n / 2 ^ 32), UInt8.ofNat (n / 2 ^ 40), UInt8.ofNat (n / 2 ^ 48),
   UInt8.ofNat (n / 2 ^ 56)]

/-- A string: its UTF-8 length, then its bytes. -/
def strB (s : String) : List UInt8 := u64B s.toByteArray.size ++ s.toByteArray.data.toList

/-- A name, prefix first (`internName` interns the prefix first). -/
def encName : ConLeche.Name → List UInt8
  | .anonymous => [0]
  | .str p s => 1 :: (encName p ++ strB s)
  | .num p n => 2 :: (encName p ++ u64B n)

/-- A list of names, one after the other (the count is the reader's). -/
def encNames : List ConLeche.Name → List UInt8
  | [] => []
  | n :: ns => encName n ++ encNames ns

/-- Every number a name carries fits a word (the encoding is exact). -/
def nameFits : ConLeche.Name → Bool
  | .anonymous => true
  | .str p s => nameFits p && decide (s.toByteArray.size < 2 ^ 63)
  | .num p n => nameFits p && decide (n < 2 ^ 64)

/-! ## Reading a byte, a number -/

section rd
variable (rom : List UInt8)

/-- Byte `k` of the ROM, as a word (`255`, no tag of any encoding, past the end). -/
def romB (k : Word) : Word := (rom[k.toNat]?.getD 255).toUInt64

theorem romB_eq (k : Word) (j : Nat) (hj : j = k.toNat) (h : j < rom.length) :
    romB rom k = rom[j].toUInt64 := by subst hj; simp [romB, h]
grind_pattern [arena_grind] romB_eq => romB rom k, rom[j]

/-- **The model of `rom_u64`**: the 8 bytes from `i` as a little-endian number. -/
def u64W (i : Word) : Word :=
  romB rom i + romB rom (i + 1) * 256 + romB rom (i + 2) * 65536 + romB rom (i + 3) * 16777216 +
    romB rom (i + 4) * 4294967296 + romB rom (i + 5) * 1099511627776 +
    romB rom (i + 6) * 281474976710656 + romB rom (i + 7) * 72057594037927936

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def romU64 : FunDecl := lfn (i) locals (x) {
  if len(rom.c8) < i + 8 || i + 8 < i { abort };
  x := le64!(rom.c8, i);
  return x
}

end rd

/-- The ROM is shorter than `2^63` bytes: every position and length is a word, and a sum of two
never wraps. -/
def RomOK (rom : List UInt8) : Prop := rom.length < 2 ^ 63

/-- `rom_u64(i)`'s check: the eight bytes from `i` are in the ROM. The models record it, so that a
model that returns read only bytes that are there (the decoder direction needs that). -/
def u64OK (rom : List UInt8) (i : Word) : Prop := i + 8 ≤ UInt64.ofNat rom.length ∧ i ≤ i + 8

instance (rom : List UInt8) (i : Word) : Decidable (u64OK rom i) := by unfold u64OK; infer_instance

section u64Val
variable (rom : List UInt8)

theorem drop_get (pos : Nat) (bs rest : List UInt8) (h : rom.drop pos = bs ++ rest) (k : Nat)
    (hk : k < bs.length) : rom[pos + k]? = bs[k]? := by
  have : (rom.drop pos)[k]? = (bs ++ rest)[k]? := by rw [h]
  rw [List.getElem?_drop, List.getElem?_append_left hk] at this
  exact this

theorem drop_len (pos : Nat) (bs rest : List UInt8) (h : rom.drop pos = bs ++ rest)
    (hb : 0 < bs.length) : pos + bs.length ≤ rom.length := by
  have := congrArg List.length h
  simp only [List.length_drop, List.length_append] at this
  have : bs.length ≤ rom.length - pos := by omega
  by_cases hp : pos ≤ rom.length
  · omega
  · have : rom.length - pos = 0 := by omega
    have hb : bs.length = 0 := by omega
    have hd : rom.drop pos = [] := List.drop_of_length_le (by omega)
    rw [hd] at h
    simp at h
    omega

theorem romB_of_drop (pos : Word) (bs rest : List UInt8) (h : rom.drop pos.toNat = bs ++ rest)
    (k : Nat) (hk : k < bs.length) (q : Word) (hq : q.toNat = pos.toNat + k) :
    romB rom q = (bs[k]'hk).toUInt64 := by
  have := drop_get rom _ _ _ h k hk
  simp only [romB, hq, this, List.getElem?_eq_getElem hk, Option.getD_some]

theorem u64W_of_drop (pos : Word) (n : Nat) (rest : List UInt8)
    (h : rom.drop pos.toNat = u64B n ++ rest) (hn : n < 2 ^ 64) (hr : RomOK rom) :
    u64W rom pos = UInt64.ofNat n := by
  have hl := drop_len rom _ _ _ h (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil, RomOK] at hl hr
  have hq : ∀ k : Nat, k < 8 → (pos + UInt64.ofNat k).toNat = pos.toNat + k := fun k hk => by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega
  have b := fun k hk q hq => romB_of_drop rom pos (u64B n) rest h k hk q hq
  have b0 := b 0 (by simp [u64B]) pos (by simp)
  have b1 := b 1 (by simp [u64B]) (pos + 1) (hq 1 (by omega))
  have b2 := b 2 (by simp [u64B]) (pos + 2) (hq 2 (by omega))
  have b3 := b 3 (by simp [u64B]) (pos + 3) (hq 3 (by omega))
  have b4 := b 4 (by simp [u64B]) (pos + 4) (hq 4 (by omega))
  have b5 := b 5 (by simp [u64B]) (pos + 5) (hq 5 (by omega))
  have b6 := b 6 (by simp [u64B]) (pos + 6) (hq 6 (by omega))
  have b7 := b 7 (by simp [u64B]) (pos + 7) (hq 7 (by omega))
  simp only [u64W, b0, b1, b2, b3, b4, b5, b6, b7]
  apply UInt64.toNat_inj.mp
  simp only [u64B, List.getElem_cons_zero, List.getElem_cons_succ, UInt8.toUInt64, UInt64.toNat_add,
    UInt64.toNat_mul, UInt64.toNat_ofNat']
  simp
  omega

theorem u64OK_of_drop (pos : Word) (n : Nat) (rest : List UInt8)
    (h : rom.drop pos.toNat = u64B n ++ rest) (hr : RomOK rom) : u64OK rom pos := by
  have hl := drop_len rom _ _ _ h (by simp [u64B])
  simp only [u64B, List.length_cons, List.length_nil, RomOK] at hl hr
  have h8 : (pos + 8).toNat = pos.toNat + 8 := by rw [UInt64.toNat_add]; simp; omega
  refine ⟨?_, ?_⟩
  · rw [UInt64.le_iff_toNat_le, h8, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]; omega
  · rw [UInt64.le_iff_toNat_le, h8]; omega

end u64Val

/-- The block load `le64` is the model `u64W`. -/
theorem le64_eq_u64W (rom : List UInt8) (i : Word) (h : i.toNat + 8 ≤ rom.length) (hw : i.toNat + 8 < 2 ^ 64) :
    le64 rom.toArray i.toNat = u64W rom i := by
  have hq : ∀ k : Nat, k < 8 → (i + UInt64.ofNat k).toNat = i.toNat + k := fun k hk => by
    rw [UInt64.toNat_add]; simp; omega
  have hb : ∀ k : Nat, k < 8 → romB rom (i + UInt64.ofNat k) = (rom.toArray[i.toNat + k]!).toUInt64 := by
    intro k hk
    simp [romB, hq k hk, List.getElem?_eq_getElem (show i.toNat + k < rom.length by omega)]
  have h0 : romB rom i = (rom.toArray[i.toNat + 0]!).toUInt64 := by
    simp [romB, List.getElem?_eq_getElem (show i.toNat < rom.length by omega)]
  simp only [u64W]
  rw [h0, show i + 1 = i + UInt64.ofNat 1 from rfl, hb 1 (by omega), show i + 2 = i + UInt64.ofNat 2 from rfl,
    hb 2 (by omega), show i + 3 = i + UInt64.ofNat 3 from rfl, hb 3 (by omega),
    show i + 4 = i + UInt64.ofNat 4 from rfl, hb 4 (by omega), show i + 5 = i + UInt64.ofNat 5 from rfl,
    hb 5 (by omega), show i + 6 = i + UInt64.ofNat 6 from rfl, hb 6 (by omega),
    show i + 7 = i + UInt64.ofNat 7 from rfl, hb 7 (by omega)]
  simp only [le64, List.range, List.range.loop, List.map, List.foldr]
  generalize rom.toArray[i.toNat + 0]! = b0
  generalize rom.toArray[i.toNat + 1]! = b1
  generalize rom.toArray[i.toNat + 2]! = b2
  generalize rom.toArray[i.toNat + 3]! = b3
  generalize rom.toArray[i.toNat + 4]! = b4
  generalize rom.toArray[i.toNat + 5]! = b5
  generalize rom.toArray[i.toNat + 6]! = b6
  generalize rom.toArray[i.toNat + 7]! = b7
  apply UInt64.toNat_inj.mp
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  simp [UInt64.toNat_add, UInt64.toNat_mul]
  omega

section u64Spec
variable (rom : List UInt8) (p : Prog) (hp : p.lookup "rom_u64" = some (romU64 rom))

include hp in
theorem romU64_spec (n : Nat) (s₀ : St) (i : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_u64" [i]
    ⦃fun r s' => s' = s₀ ∧ u64OK rom i ∧ r = [u64W rom i]; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, romU64]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld8x8]
    all_goals (simp_all [Mem.src8, St.setLoc, Cmp.eval, Locals.init, Sig.retVal, Sig.retOr, u64OK, BinOp.eval])
    all_goals (refine le64_eq_u64W rom i (by assumption) ?_)
    all_goals (rename_i h _; have := UInt64.le_iff_toNat_le.mp h; rw [UInt64.toNat_add] at this
               simp at this; have := i.toNat_lt; omega)

end u64Spec

/-! ## `rom_put(i, l)`: ROM bytes to the pool top -/

section put
variable (rom : List UInt8)

/-- The model of the copy loop: ROM bytes `i + j ‥ i + l` to `POOL⟨pt⟩[pb + j ‥ pb + l]`. -/
def rputW (m : Mem) (pt pb i l j : Word) : Mem :=
  if j < l then rputW (m.set64 (tierA 0 pt) (pb + j) (romB rom (i + j))) pt pb i l (j + 1) else m
termination_by l.toNat - j.toNat
decreasing_by
  have : j.toNat < l.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹j < l›
  have := l.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

theorem rputW_end (m : Mem) (pt pb i l j : Word) (hj : ¬ j < l) : rputW rom m pt pb i l j = m := by
  rw [rputW]; simp only [hj, ↓reduceIte]

theorem rputW_step (m m' : Mem) (pt pb i l j j' : Word) (hj : j < l) (hj' : j' = j + 1)
    (hm' : m' = m.set64 (tierA 0 pt) (pb + j) (romB rom (i + j))) :
    rputW rom m pt pb i l j = rputW rom m' pt pb i l j' := by
  subst hj' hm'
  rw [rputW]; simp only [hj, ↓reduceIte]

grind_pattern [arena_grind] rputW_end => rputW rom m pt pb i l j
grind_pattern [arena_grind] rputW_step => rputW rom m pt pb i l j, rputW rom m' pt pb i l j'

/-- Every ROM byte in `[i + j, i + l)` is ASCII (below `128`). -/
def asciiW (i l j : Word) : Bool :=
  if j < l then decide (romB rom (i + j) < 128) && asciiW i l (j + 1) else true
termination_by l.toNat - j.toNat
decreasing_by
  have : j.toNat < l.toNat := by simpa [UInt64.lt_iff_toNat_lt] using ‹j < l›
  have := l.toNat_lt
  have : (j + 1).toNat = j.toNat + 1 := by
    rw [UInt64.toNat_add]; simp; omega
  omega

theorem asciiW_end (i l j : Word) (hj : ¬ j < l) : asciiW rom i l j = true := by
  rw [asciiW]; simp only [hj, ↓reduceIte]

theorem asciiW_step (i l j j' : Word) (hj : j < l) (hj' : j' = j + 1) (hb : romB rom (i + j) < 128) :
    asciiW rom i l j = asciiW rom i l j' := by
  subst hj'
  rw [asciiW]; simp [hj, hb]

end put

grind_pattern [arena_grind] asciiW_end => asciiW rom i l j
grind_pattern [arena_grind] asciiW_step => asciiW rom i l j, asciiW rom i l j'

section putProg
variable (rom : List UInt8)

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
-- The names' strings must be ASCII (`scan!` for a byte `≥ 128`): then the bytes are some
-- `String`'s UTF-8 (the pin data is untrusted, DESIGN.md "The pin data as an input"); they go to
-- the pool top as one block (`copy!`; lane blkcopy2).
def romPut : FunDecl := lfn (i, l) locals (top, j, pt, pb, e) {
  if len(rom.c8) < i + l || i + l < i { abort };
  e := i + l;
  j := scan!(rom.c8, i, e, hiC);
  if j != e { abort };
  top := CTL.u64[0];
  pt := ⦃top⦄.tier;
  pb := ⦃top⦄.idx;
  if len(POOL⟨pt⟩) < pb { abort };
  if len(POOL⟨pt⟩) - pb < l { abort };
  copy!(POOL.u64⟨pt⟩, pb, rom.c8, i, l);
  CTL.u64[0] := top + l;
  return top
}

variable (p : Prog)

/-- A scan for a byte `≥ 128` that runs to the end: the range is ASCII. -/
theorem asciiW_scan (i l : Word) (hv : i.toNat + l.toNat < 2 ^ 64) (hr : i.toNat + l.toNat ≤ rom.length) :
    ∀ (d : Nat) (j : Word), l.toNat - j.toNat = d → j ≤ l →
      scanN rom.toArray hiC (i.toNat + j.toNat) (i.toNat + l.toNat) = i.toNat + l.toNat →
      asciiW rom i l j = true := by
  intro d
  induction d with
  | zero =>
    intro j hd hj _
    exact asciiW_end rom i l j (by rw [UInt64.lt_iff_toNat_lt]; omega)
  | succ d ih =>
    intro j hd hj hs
    have hjl : j.toNat < l.toNat := by omega
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by have := l.toNat_lt; simp; omega)
    have hlt : i.toNat + j.toNat < i.toNat + l.toNat := by omega
    have hc : hiC[(rom.toArray[i.toNat + j.toNat]!).toNat]! = 0 := by
      rcases Decidable.em (hiC[(rom.toArray[i.toNat + j.toNat]!).toNat]! = 0) with h | h
      · exact h
      · rw [scanN_hit _ _ _ _ hlt h] at hs; omega
    have hb : rom.toArray[i.toNat + j.toNat]! < 128 := by
      have := mt (hiC_mem (rom.toArray[i.toNat + j.toNat]!)).mpr (by simpa using hc)
      exact UInt8.not_le.mp this
    have hij : (i + j).toNat = i.toNat + j.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [asciiW_step rom i l j (j + 1) (UInt64.lt_iff_toNat_lt.mpr hjl) rfl ?_]
    · apply ih (j + 1) (by omega) (UInt64.le_iff_toNat_le.mpr (by omega))
      rw [hj1, ← Nat.add_assoc, ← scanN_miss _ _ _ _ hlt hc]; exact hs
    · rw [romB_eq rom _ _ hij.symm (by omega)]
      have : rom.toArray[i.toNat + j.toNat]! = rom[i.toNat + j.toNat] := by
        rw [getElem!_pos rom.toArray _ (by simp; omega)]; simp
      rw [this] at hb
      exact UInt64.lt_iff_toNat_lt.mpr (by simp; exact hb)

/-- The copy block is the per-word model `rputW`. -/
theorem rputW_copy (pt pb i l : Word) (hv : i.toNat + l.toNat < 2 ^ 64)
    (hr : i.toNat + l.toNat ≤ rom.length) :
    ∀ (d : Nat) (m : Mem) (j : Word), l.toNat - j.toNat = d → j ≤ l →
      rputW rom m pt pb i l j = m.copy8w (tierA 0 pt) (pb + j) rom.toArray (i + j) d := by
  intro d
  induction d with
  | zero =>
    intro m j hd hj
    rw [rputW_end rom m pt pb i l j (by rw [UInt64.lt_iff_toNat_lt]; omega), Mem.copy8w_zero]
  | succ d ih =>
    intro m j hd hj
    have hjl : j.toNat < l.toNat := by omega
    have hj1 : (j + 1).toNat = j.toNat + 1 := by
      rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by have := l.toNat_lt; simp; omega)
    have hij : (i + j).toNat = i.toNat + j.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
    rw [rputW, ite_eq_left (UInt64.lt_iff_toNat_lt.mpr hjl),
      ih _ (j + 1) (by omega) (UInt64.le_iff_toNat_le.mpr (by omega)), Mem.copy8w_succ,
      romB_eq rom _ _ hij.symm (by omega), getElem!_pos rom.toArray _ (by simp; omega),
      UInt64.add_assoc, UInt64.add_assoc]
    simp [hij]

/-- `rom_put`'s checks: an ASCII range of the ROM that fits above the pool top. -/
def romPutOK (m : Mem) (i l : Word) : Prop :=
  i + l ≤ UInt64.ofNat rom.length ∧ i ≤ i + l ∧
    (m.top &&& (1099511627775 : Word)) ≤ m.len64 (tierA 0 (m.top >>> 40)) ∧
    l ≤ m.len64 (tierA 0 (m.top >>> 40)) - (m.top &&& 1099511627775) ∧
    asciiW rom i l 0 = true

instance (m : Mem) (i l : Word) : Decidable (romPutOK rom m i l) := by
  unfold romPutOK; infer_instance

theorem rputW_size (pt pb i l : Word) (b : ArrId) :
    ∀ (d : Nat) (m : Mem) (j : Word), l.toNat - j.toNat = d →
      ((rputW rom m pt pb i l j).arr64 b).size = (m.arr64 b).size := by
  intro d
  induction d with
  | zero =>
    intro m j hd
    have hjn : ¬ j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [rputW_end _ _ _ _ _ _ _ hjn]
  | succ d ih =>
    intro m j hd
    have hjn : j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have := l.toNat_lt
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [rputW]; simp only [hjn, ↓reduceIte]
    rw [ih _ _ (by omega), size_set64]

@[arena_grind =] theorem rputW_pcap (m : Mem) (pt pb i l j : Word) :
    pcap (rputW rom m pt pb i l j) = pcap m :=
  pcap_congr (rputW_size rom pt pb i l POOL _ m j rfl) (rputW_size rom pt pb i l POOL1 _ m j rfl)

theorem romPutOK_room (m : Mem) (i l : Word) (h : romPutOK rom m i l)
    (hs : (m.arr64 (tierA 0 (m.top >>> 40))).size < 2 ^ 63) :
    (m.top &&& 1099511627775).toNat + l.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size := by
  obtain ⟨-, -, h3, h4, -⟩ := h
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact L.Front.toNat_ofNat_size _ hs
  have := UInt64.le_iff_toNat_le.mp h4
  have := UInt64.le_iff_toNat_le.mp h3
  rw [UInt64.toNat_sub_of_le _ _ h3, hlen] at *
  omega

/-- `rom_put`'s checks bound the appended slice by the pool's capacity, for a top in one of the
two tiers. -/
theorem romPutOK_cap (m : Mem) (i l : Word) (h : romPutOK rom m i l) (hc : pcap m < 2 ^ 64)
    (ht : m.top.toNat < 2 ^ 41) : m.top.toNat + l.toNat ≤ pcap m := by
  have hsz := pcap_tier m (m.top >>> 40) hc
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top ht
  have hroom := romPutOK_room rom m i l h (by omega)
  rw [pcap_eq m hc]
  omega
grind_pattern [arena_grind] romPutOK_cap => romPutOK rom m i l, pcap m

theorem romPut_specW (hp : p.lookup "rom_put" = some (romPut rom)) (n : Nat) (s₀ : St) (i l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_put" [i, l]
    ⦃fun r s' => LocEq s' s₀ ∧ romPutOK rom s₀.mem i l ∧ r = [s₀.mem.top] ∧
      s'.mem = (rputW rom s₀.mem (s₀.mem.top >>> 40) (s₀.mem.top &&& 1099511627775) i l 0).set64 CTL 0
        (s₀.mem.top + l) ∧
      (s'.mem.arr64 POOL).size = (s₀.mem.arr64 POOL).size; ⊤⦄ := by
  have hsz := fun m pt pb => rputW_size rom pt pb i l POOL _ m 0 rfl
  rw [invoke_eq _ hp]
  simp only [callFn, romPut]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, evalE, evalC, evalArgs, setLoc, ld64, st64, warr]
    all_goals (try simp only [St.setLoc_loc, St.setLoc_mem, Locals.init_nil,
      Locals.init_cons_zero, Locals.init_cons_succ, Cmp.eval, BinOp.eval, Nat.reduceEqDiff,
      reduceIte, bne_iff_ne, ne_eq, decide_eq_true_eq, Mem.src8, not_true_eq_false,
      Decidable.not_not] at *)
    all_goals (
      have hv' : i ≤ i + l := UInt64.not_lt.mp (by simpa using ‹¬decide (i + l < i) = true›)
      have hr' : i + l ≤ UInt64.ofNat rom.length :=
        UInt64.not_lt.mp (by simpa using ‹¬decide (UInt64.ofNat rom.length < i + l) = true›)
      have hb : UInt64.toNat (i + l) ≤ rom.toArray.size := ‹i ≤ i + l ∧ UInt64.toNat (i + l) ≤ rom.toArray.size›.2
      have hs : UInt64.ofNat (scanN rom.toArray hiC (UInt64.toNat i) (UInt64.toNat (i + l))) = i + l := ‹_›
      have hil : (i + l).toNat = i.toNat + l.toNat := by
        have h1 := UInt64.le_iff_toNat_le.mp hv'; have := i.toNat_lt; have := l.toNat_lt
        rw [UInt64.toNat_add] at h1 ⊢; omega
      have hlen : (i + l).toNat ≤ rom.length := by simpa using hb
      have hv2 : i.toNat + l.toNat < 2 ^ 64 := by have := (i + l).toNat_lt; omega
      have hs' : scanN rom.toArray hiC (i.toNat + (0 : Word).toNat) (i.toNat + l.toNat) =
          i.toNat + l.toNat := by
        have := congrArg UInt64.toNat hs
        rw [hil, UInt64.toNat_ofNat'] at this
        have := scanN_le_end rom.toArray hiC i.toNat (i.toNat + l.toNat) (by omega)
        simp only [UInt64.toNat_zero, Nat.add_zero]; omega
      have has := asciiW_scan rom i l hv2 (by omega) _ 0 rfl (UInt64.le_iff_toNat_le.mpr (by simp)) hs'
      have hcp := rputW_copy rom (s₀.mem.top >>> 40) (s₀.mem.top &&& 1099511627775) i l hv2
        (by omega) _ s₀.mem 0 rfl (UInt64.le_iff_toNat_le.mpr (by simp))
      simp only [UInt64.add_zero, Nat.sub_zero, UInt64.toNat_zero] at hcp
      first
        | (simp only [Sig.retVal, Sig.retOr, Mem.top, List.cons.injEq, and_true]
           rw [Array.getElem?_eq_getElem]; rfl)
        | grind [romPutOK, LocEq, Mem.top, Sig.retVal, Mem.size64_set64])

end putProg

/-! ## `rom_put`'s memory -/

section putFacts
variable (rom : List UInt8)

/-- ROM byte `k`, as a word (`0` past the end), by a natural-number position. -/
def romN (k : Nat) : Word := (rom[k]?.getD 255).toUInt64

theorem rputW_facts (pt pb i n : Word) (hv : i.toNat + n.toNat < 2 ^ 64) (ht : pt.toNat ≤ 1) :
    ∀ (d : Nat) (m : Mem) (j : Word), n.toNat - j.toNat = d → j ≤ n →
      pb.toNat + n.toNat ≤ (m.arr64 (tierA 0 pt)).size → (m.arr64 (tierA 0 pt)).size ≤ 2 ^ 40 →
      PFrame m (rputW rom m pt pb i n j) ∧
      ∀ x, (vpool (rputW rom m pt pb i n j))[x]? =
        if pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x ∧ x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat then
          some (romN rom (i.toNat + (x - (pt.toNat * 2 ^ 40 + pb.toNat))))
        else (vpool m)[x]? := by
  intro d
  induction d with
  | zero =>
    intro m j hd hj _ _
    have hjn : ¬ j < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [rputW_end _ _ _ _ _ _ _ hjn]
    refine ⟨PFrame.refl _, fun x => ?_⟩
    have : ¬ (pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x ∧
        x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat) := by
      have := UInt64.le_iff_toNat_le.mp hj; omega
    simp [this]
  | succ d ih =>
    intro m j hd hj hp hs
    have hjn : j < n := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have hpj : (pb + j).toNat = pb.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    have hvj : (i + j).toNat = i.toNat + j.toNat := by rw [UInt64.toNat_add]; simp; omega
    rw [rputW]; simp only [hjn, ↓reduceIte]
    have hsz : ((m.set64 (tierA 0 pt) (pb + j) (romB rom (i + j))).arr64 (tierA 0 pt)).size =
        (m.arr64 (tierA 0 pt)).size :=
      size_set64 _ _ _ _ _
    obtain ⟨hf, hx⟩ := ih (m.set64 (tierA 0 pt) (pb + j) (romB rom (i + j))) (j + 1) (by omega)
      (UInt64.le_iff_toNat_le.mpr (by omega)) (by omega) (by omega)
    refine ⟨PFrame.trans (PFrame.set64 _ _ _ (PFrame.refl _)) hf, fun x => ?_⟩
    rw [hx, vpool_set64t m pt (pb + j) _ ht (by omega) hs, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds]
    simp only [hpj, hj1, vpool_size]
    by_cases h1 : pt.toNat * 2 ^ 40 + pb.toNat + (j.toNat + 1) ≤ x ∧
        x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat
    · have h2 : pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) ≠ x := by omega
      simp [h1, show pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x by omega]
    · by_cases h2 : pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) = x
      · subst h2
        have e : pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) - (pt.toNat * 2 ^ 40 + pb.toNat) = j.toNat := by
          omega
        simp [show pt.toNat * 2 ^ 40 + (pb.toNat + j.toNat) < 2 ^ 41 by omega, romB, romN, hvj, e]
        try omega
      · have : ¬ (pt.toNat * 2 ^ 40 + pb.toNat + j.toNat ≤ x ∧
            x < pt.toNat * 2 ^ 40 + pb.toNat + n.toNat) := by omega
        simp [h1, h2, this]

/-- **`rom_put`'s memory**: the pool grew by the ROM bytes `[i, i + l)`, at the old top. -/
theorem romPutW_facts (m : Mem) (i l : Word) (hpool : PoolOK m) (hok : romPutOK rom m i l)
    (hr : RomOK rom) :
    Grows m ((rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).set64 CTL 0 (m.top + l)) ∧
    SliceOK ((rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).set64 CTL 0 (m.top + l))
      m.top l ∧
    sliceL (vpool ((rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).set64 CTL 0
      (m.top + l))) m.top.toNat l.toNat =
      ((rom.drop i.toNat).take l.toNat).map UInt8.toUInt64 ∧
    i.toNat + l.toNat ≤ rom.length := by
  have hsm := hpool.small
  have h41 := hpool.top41
  have hsz := hsm.tier (m.top >>> 40)
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top h41
  have hctl0 : 0 < (m.arr64 CTL).size := hpool.2.1
  obtain ⟨h1, h1', h3, h4, -⟩ := hok
  simp only [RomOK] at hr
  have hil : (i + l).toNat = i.toNat + l.toNat := by
    have := UInt64.le_iff_toNat_le.mp h1'
    have := i.toNat_lt; have := l.toNat_lt
    have e := UInt64.toNat_add i l
    rw [show (2:Nat)^64 = 18446744073709551616 from rfl] at *
    omega
  have hin : i.toNat + l.toNat ≤ rom.length := by
    have := UInt64.le_iff_toNat_le.mp h1
    rw [hil, UInt64.toNat_ofNat'] at this
    rwa [Nat.mod_eq_of_lt (by omega)] at this
  have hlen : (m.len64 (tierA 0 (m.top >>> 40))).toNat = (m.arr64 (tierA 0 (m.top >>> 40))).size := by
    simp only [Mem.len64]; exact L.Front.toNat_ofNat_size _ (by omega)
  have hroom : l.toNat ≤ (m.arr64 (tierA 0 (m.top >>> 40))).size - (m.top &&& 1099511627775).toNat := by
    have := UInt64.le_iff_toNat_le.mp h4
    rwa [UInt64.toNat_sub_of_le _ _ h3, hlen] at this
  have h3' := UInt64.le_iff_toNat_le.mp h3
  rw [hlen] at h3'
  obtain ⟨hf, hx⟩ := rputW_facts rom (m.top >>> 40) (m.top &&& 1099511627775) i l (by omega) htier
    _ m 0 rfl (UInt64.le_iff_toNat_le.mpr (by simp)) (by omega) (by omega)
  simp only [UInt64.toNat_zero, Nat.add_zero, hsplit] at hx
  have hctl : 0 < ((rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).arr64 CTL).size := by
    rw [hf.ctl]; exact hctl0
  have htop' := Mem.top_set64 _ (m.top + l) hctl
  have hg := Grows.write m _ l hpool hf (fun x hxt => by rw [hx, ite_eq_right (by omega)]) (by omega)
  refine ⟨hg, SliceOK.fresh hg htop', ?_, hin⟩
  rw [vpool_set64_ne _ _ _ _ ⟨by decide, by decide⟩, sliceL, List.ext_getElem_iff]
  refine ⟨by simp; omega, fun k hk₁ hk₂ => ?_⟩
  simp only [List.length_ofFn] at hk₁
  simp only [List.getElem_ofFn, hx, List.getElem_map, List.getElem_take, List.getElem_drop]
  simp [show m.top.toNat + k < m.top.toNat + l.toNat by omega, romN,
    show i.toNat + k < rom.length by omega]

end putFacts

/-! ## `rom_name(pos)`: intern the name encoded at `pos` -/

section nameProg
variable (rom : List UInt8)

/-- `rom_put`'s model: the slice's offset and the memory after. -/
def romPutW (m : Mem) (i l : Word) : Option (Word × Mem) :=
  if romPutOK rom m i l then some (m.top, (rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).set64 CTL 0 (m.top + l))
  else none

/-- After the `anonymous` node. -/
def nmAnonK (pos : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, m') => if 4294967296 ≤ h then none else some (h, pos + 1, m')

/-- After a `str` node's string was interned. -/
def nmStr2K (q l : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h', m₃) => if 4294967296 ≤ h' then none else some (h', q + 8 + l, m₃)

/-- After a `str` node's string went to the pool: intern it. -/
def nmStrK (h q l : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (o, m₂) => nmStr2K q l (nsinternW m₂ h o l)

/-- After a `num` node's number. -/
def nmNumK (q : Word) : Option (Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h', m₂) => if 4294967296 ≤ h' then none else some (h', q + 8, m₂)

/-- After the prefix. -/
def nmRecK (t : Word) : Option (Word × Word × Mem) → Option (Word × Word × Mem)
  | none => none
  | some (h, q, m₁) =>
    if ¬ u64OK rom q then none
    else if t = 1 then nmStrK h q (u64W rom q) (romPutW rom m₁ (q + 8) (u64W rom q))
    else if t = 2 then nmNumK q (nninternW m₁ h (u64W rom q))
    else none

/-- **The model of `rom_name`** at L fuel `n`: the handle, the position after, the memory after. -/
def romNameW : Nat → Mem → Word → Option (Word × Word × Mem)
  | 0, _, _ => none
  | n + 1, m, pos =>
    if romB rom pos = 0 then nmAnonK pos (nainternW m)
    else nmRecK rom (romB rom pos) (romNameW n m (pos + 1))

theorem romNameW_anon (n : Nat) (m : Mem) (pos : Word) (h0 : romB rom pos = 0) :
    romNameW rom (n + 1) m pos = nmAnonK pos (nainternW m) := by simp [romNameW, h0]
theorem romNameW_rec (n : Nat) (m : Mem) (pos : Word) (h0 : romB rom pos ≠ 0) :
    romNameW rom (n + 1) m pos = nmRecK rom (romB rom pos) (romNameW rom n m (pos + 1)) := by
  simp [romNameW, h0]

/-- con-ron: none — the ROM reader (L has constant bytes where the twin has con-leche values) -/
def romName : FunDecl := lfn (pos) locals (t, h, q, l, o) {
  t := rom.c8[pos];
  if t == 0 {
    h := call intern_nanon();
    if h >= 4294967296 { abort };
    return (h, pos + 1)
  };
  (h, q) := call rom_name(pos + 1);
  l := call rom_u64(q);
  if t == 1 {
    o := call rom_put(q + 8, l);
    h := call intern_nstr(h, o, l);
    if h >= 4294967296 { abort };
    return (h, q + 8 + l)
  };
  if t != 2 { abort };
  h := call intern_nnum(h, l);
  if h >= 4294967296 { abort };
  return (h, q + 8)
}

end nameProg

section nameArms
variable (rom : List UInt8) (h q l t pos o h' : Word) (m m₁ m₂ m₃ : Mem)
theorem nmAnonK_some (hh : ¬ 4294967296 ≤ h) : nmAnonK pos (some (h, m)) = some (h, pos + 1, m) := by
  simp [nmAnonK, hh]
theorem nmStrK_some : nmStrK h q l (some (o, m₂)) = nmStr2K q l (nsinternW m₂ h o l) := rfl
theorem nmStr2K_some (hh : ¬ 4294967296 ≤ h') : nmStr2K q l (some (h', m₃)) = some (h', q + 8 + l, m₃) := by
  simp [nmStr2K, hh]
theorem nmNumK_some (hh : ¬ 4294967296 ≤ h') : nmNumK q (some (h', m₂)) = some (h', q + 8, m₂) := by
  simp [nmNumK, hh]
theorem nmRecK_str (ht : t = 1) (hu : u64OK rom q) :
    nmRecK rom t (some (h, q, m₁)) = nmStrK h q (u64W rom q) (romPutW rom m₁ (q + 8) (u64W rom q)) := by
  simp [nmRecK, ht, hu]
theorem nmRecK_num (ht : t = 2) (hu : u64OK rom q) :
    nmRecK rom t (some (h, q, m₁)) = nmNumK q (nninternW m₁ h (u64W rom q)) := by simp [nmRecK, ht, hu]
theorem romPutW_ok (hok : romPutOK rom m (q + 8) l) :
    romPutW rom m (q + 8) l = some (m.top, (rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) (q + 8) l 0).set64 CTL 0 (m.top + l)) := by
  simp only [romPutW]; rw [ite_eq_left hok]
end nameArms

attribute [arena_grind =] nmAnonK_some nmNumK_some nmRecK_str nmRecK_num romPutW_ok nmStrK_some
  nmStr2K_some
grind_pattern [arena_grind] romPutOK_room => romPutOK rom m i l, (m.arr64 (tierA 0 (m.top >>> 40))).size
grind_pattern [arena_grind] romNameW_anon => romNameW rom (n + 1) m pos
grind_pattern [arena_grind] romNameW_rec => romNameW rom (n + 1) m pos

/-! ## The ROM readers keep the top in one of the two tiers -/

/-- An intern of the store library leaves the pool top (`CTL[0]`) and the pool's capacity alone. -/
theorem consInternM_top {C : ConsSch} (hW : C.WF) (hc : C.ca ≠ 0) (hc1 : C.ca + 1 ≠ 0) {m m' : Mem}
    {ks : List Word} {w : Word} (h : consInternM C m ks = some (w, m')) :
    m'.top = m.top ∧ pcap m' = pcap m := by
  have hf := consInternM_frame hW h
  refine ⟨?_, pcap_congr (hf.2.2.1 _) (hf.2.2.1 _)⟩
  have := hf.2.1 0 (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (e | e) <;> first | exact hc e.symm | exact hc1 e.symm)
  simpa [Mem.top, rdW] using this

theorem top_set64_lt (m : Mem) (v : Word) (hv : v.toNat < 2 ^ 41) : (m.set64 CTL 0 v).top.toNat < 2 ^ 41 := by
  by_cases h : 0 < (m.arr64 CTL).size
  · rw [Mem.top_set64 _ _ h]; exact hv
  · have e : (m.set64 CTL 0 v).arr64 CTL = (m.arr64 CTL).set! 0 v := Mem.arr64_set64_same _ _ _ _
    simp only [Mem.top, e, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [h]

theorem top_set64_ne (m : Mem) (c v : Word) (hc : c.toNat ≠ 0) : (m.set64 CTL c v).top = m.top := by
  have e : (m.set64 CTL c v).arr64 CTL = (m.arr64 CTL).set! c.toNat v := Mem.arr64_set64_same _ _ _ _
  simp only [Mem.top, e, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  simp [hc]

theorem top_set64_ctl (m : Mem) (c v : Word) (hc : c.toNat ≠ 0) : (m.set64 CTL c v).top = m.top :=
  top_set64_ne m c v hc
grind_pattern [arena_grind] top_set64_ctl => (m.set64 CTL c v).top

theorem top_set64_arr (m : Mem) (b : ArrId) (i v : Word) (hb : b ≠ CTL) : (m.set64 b i v).top = m.top := by
  simp only [Mem.top, Mem.arr64_set64_ne _ _ _ _ _ (Ne.symm hb)]
grind_pattern [arena_grind] top_set64_arr => (m.set64 b i v).top

theorem Keep.pcap {m m' : Mem} (h : Keep m m') : pcap m' = pcap m := pcap_congr (h.size _) (h.size _)
grind_pattern [arena_grind] Keep.pcap => Keep m m', pcap m'

/-- `m'` keeps the pool's capacity, a top in a tier stays in a tier, and so does the mode
(`ModeOK`: outside the scratch tier the top is in tier 0). -/
def TopK (m m' : Mem) : Prop :=
  pcap m < 2 ^ 64 → m.top.toNat < 2 ^ 41 →
    m'.top.toNat < 2 ^ 41 ∧ pcap m' = pcap m ∧ (ModeOK m → ModeOK m')

theorem TopK.refl (m : Mem) : TopK m m := fun _ ht => ⟨ht, rfl, id⟩

theorem TopK.trans {m m₁ m₂ : Mem} (h₁ : TopK m m₁) (h₂ : TopK m₁ m₂) : TopK m m₂ := fun hc ht =>
  have ⟨a, b, e⟩ := h₁ hc ht
  have ⟨c, d, f⟩ := h₂ (by rw [b]; exact hc) a
  ⟨c, d.trans b, fun h => f (e h)⟩

theorem TopK.of_eq {m m' : Mem} (ht : m'.top = m.top) (hp : pcap m' = pcap m) (hf : m'.flag = m.flag) :
    TopK m m' :=
  fun _ h => ⟨ht ▸ h, hp, fun hm => by unfold ModeOK at *; rw [ht, hf]; exact hm⟩

theorem memFrame_top {A : List ArrId} {C : List Word} {m m' : Mem} (h : MemFrame A C m m')
    (h0 : (0 : Word) ∉ C) (h1 : (1 : Word) ∉ C := by decide) : TopK m m' :=
  TopK.of_eq (by simpa [Mem.top, rdW] using h.2.1 0 h0) (pcap_congr (h.2.2.1 _) (h.2.2.1 _))
    (by simpa [Mem.flag, rdW] using h.2.1 1 h1)

theorem cons_topK {C : ConsSch} (hW : C.WF) (hc : C.ca ≠ 0) (hc1 : C.ca + 1 ≠ 0) {m m' : Mem}
    {ks : List Word} {w : Word} (h : consInternM C m ks = some (w, m'))
    (hd : C.ca ≠ 1 := by decide) (hd1 : C.ca + 1 ≠ 1 := by decide) : TopK m m' :=
  memFrame_top (consInternM_frame hW h)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (e | e) <;> first | exact hc e.symm | exact hc1 e.symm)
    (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro (e | e) <;> first | exact hd e.symm | exact hd1 e.symm)

theorem rputW_arr (rom : List UInt8) (pt pb i l : Word) (b : ArrId) (hb : b ≠ POOL ∧ b ≠ POOL1) :
    ∀ (d : Nat) (m : Mem) (j : Word), l.toNat - j.toNat = d →
      (rputW rom m pt pb i l j).arr64 b = m.arr64 b := by
  intro d
  induction d with
  | zero =>
    intro m j hd
    have hjn : ¬ j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    rw [rputW_end _ _ _ _ _ _ _ hjn]
  | succ d ih =>
    intro m j hd
    have hjn : j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    have hjn' := UInt64.lt_iff_toNat_lt.mp hjn
    have := l.toNat_lt
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [rputW]; simp only [hjn, ↓reduceIte]
    rw [ih _ _ (by omega), arr64_set64_tier_ne _ _ _ _ _ hb]

theorem top_set64_cases (m : Mem) (v : Word) :
    (m.set64 CTL 0 v).top = v ∨ (m.set64 CTL 0 v).top = m.top := by
  by_cases h : 0 < (m.arr64 CTL).size
  · exact .inl (Mem.top_set64 _ _ h)
  · right
    have e : (m.set64 CTL 0 v).arr64 CTL = (m.arr64 CTL).set! 0 v := Mem.arr64_set64_same _ _ _ _
    simp only [Mem.top, e, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp [h]

/-- **`rom_put`'s memory keeps the top in its tier**, the capacity and the mode. -/
theorem romPut_topK (rom : List UInt8) {m : Mem} {i l : Word} (hok : romPutOK rom m i l) :
    TopK m ((rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).set64 CTL 0 (m.top + l)) := by
  intro hc ht
  have hsz := pcap_tier m (m.top >>> 40) hc
  have hsplit := tag_split m.top
  have htier := tag_tier_le m.top ht
  have hroom := romPutOK_room rom m i l hok (by omega)
  have hT : (m.top + l).toNat = m.top.toNat + l.toNat := by
    rw [UInt64.toNat_add]; simp; omega
  have hctl : (rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).arr64 CTL = m.arr64 CTL :=
    rputW_arr rom _ _ _ _ CTL ⟨by decide, by decide⟩ _ m 0 rfl
  have hflag : ((rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).set64 CTL 0 (m.top + l)).flag
      = m.flag := by rw [Mem.flag_set64_top]; simp only [Mem.flag, hctl]
  have htop0 : (rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0).top = m.top :=
    congrArg (fun a : Array Word => a[0]?.getD 0) hctl
  refine ⟨?_, by rw [pcap_set64, rputW_pcap], fun hm => ?_⟩
  · rcases top_set64_cases (rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0) (m.top + l) with e | e
    · rw [e, hT]; omega
    · rw [e, htop0]; exact ht
  · rcases hm with hf | h0
    · exact .inl (by rw [hflag]; exact hf)
    · right
      rcases top_set64_cases (rputW rom m (m.top >>> 40) (m.top &&& 1099511627775) i l 0) (m.top + l) with e | e
      · rw [e, hT]; omega
      · rw [e, htop0]; exact h0

/-- **`rom_name`'s model keeps the top in a tier**, the pool's capacity and the mode. -/
theorem romNameW_top (rom : List UInt8) : ∀ (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem),
    romNameW rom n m pos = some (h, q, m') → TopK m m' := by
  intro n
  induction n with
  | zero => intro m pos h q m' hW; simp [romNameW] at hW
  | succ n ih =>
    intro m pos h q m' hW
    by_cases h0 : romB rom pos = 0
    · rw [romNameW_anon rom n m pos h0] at hW
      cases hI : nainternW m with
      | none => rw [hI] at hW; simp [nmAnonK] at hW
      | some r =>
        obtain ⟨w, m₁⟩ := r
        rw [hI] at hW
        simp only [nmAnonK] at hW
        split at hW
        · simp at hW
        simp only [Option.some.injEq, Prod.mk.injEq] at hW
        obtain ⟨-, -, rfl⟩ := hW
        exact cons_topK nanonCS_wf (by decide) (by decide) hI
    · rw [romNameW_rec rom n m pos h0] at hW
      cases hP : romNameW rom n m (pos + 1) with
      | none => rw [hP] at hW; simp [nmRecK] at hW
      | some r =>
        obtain ⟨h₁, q₁, m₁⟩ := r
        have k1 := ih m (pos + 1) h₁ q₁ m₁ hP
        rw [hP] at hW
        simp only [nmRecK] at hW
        split at hW
        · simp at hW
        split at hW
        · simp only [romPutW] at hW
          split at hW
          · rename_i hok
            simp only [nmStrK] at hW
            cases hI : nsinternW ((rputW rom m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) (q₁ + 8)
                (u64W rom q₁) 0).set64 CTL 0 (m₁.top + u64W rom q₁)) h₁ m₁.top (u64W rom q₁) with
            | none => rw [hI] at hW; simp [nmStr2K] at hW
            | some r =>
              obtain ⟨w, m₃⟩ := r
              rw [hI] at hW
              simp only [nmStr2K] at hW
              split at hW
              · simp at hW
              simp only [Option.some.injEq, Prod.mk.injEq] at hW
              obtain ⟨-, -, rfl⟩ := hW
              exact (k1.trans (romPut_topK rom hok)).trans (cons_topK nstrCS_wf (by decide) (by decide) hI)
          · simp [nmStrK] at hW
        split at hW
        · simp only [nmNumK] at hW
          cases hI : nninternW m₁ h₁ (u64W rom q₁) with
          | none => rw [hI] at hW; simp at hW
          | some r =>
            obtain ⟨w, m₃⟩ := r
            rw [hI] at hW
            simp only at hW
            split at hW
            · simp at hW
            simp only [Option.some.injEq, Prod.mk.injEq] at hW
            obtain ⟨-, -, rfl⟩ := hW
            exact k1.trans (cons_topK nnumCS_wf (by decide) (by decide) hI)
        · simp at hW

theorem TopK.mode {m m' : Mem} (h : TopK m m') (hp : PoolOK m) (hmo : ModeOK m) : ModeOK m' :=
  (h (by have := hp.2.2.1; omega) hp.top41).2.2 hmo

theorem romNameW_topK {rom : List UInt8} {n : Nat} {m : Mem} {pos h q : Word} {m' : Mem}
    (hW : romNameW rom n m pos = some (h, q, m')) : TopK m m' := romNameW_top rom n m pos h q m' hW
theorem romNameW_top' (rom : List UInt8) (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem)
    (hW : romNameW rom n m pos = some (h, q, m')) (hc : pcap m < 2 ^ 64) (ht : m.top.toNat < 2 ^ 41) :
    m'.top.toNat < 2 ^ 41 := (romNameW_top rom n m pos h q m' hW hc ht).1
grind_pattern [arena_grind] romNameW_top' => romNameW rom n m pos, some (h, q, m')

/-- The functions `rom_name` calls. -/
structure NameProg (rom : List UInt8) (p : Prog) : Prop where
  rom_name : p.lookup "rom_name" = some (romName rom)
  rom_u64 : p.lookup "rom_u64" = some (romU64 rom)
  rom_put : p.lookup "rom_put" = some (romPut rom)
  nanon_find : p.lookup "nanon_find" = some nanonFind
  nanon_push : p.lookup "nanon_push" = some nanonPush
  intern_nanon : p.lookup "intern_nanon" = some internNAnon
  lit_hash : p.lookup "lit_hash" = some litHash
  limbs_eq : p.lookup "limbs_eq" = some limbsEq
  nstr_match : p.lookup "nstr_match" = some nsMatch
  nstr_find : p.lookup "nstr_find" = some nsFind
  nstr_push : p.lookup "nstr_push" = some nsPush
  intern_nstr : p.lookup "intern_nstr" = some internNStr
  nnum_find : p.lookup "nnum_find" = some nnumFind
  nnum_push : p.lookup "nnum_push" = some nnumPush
  intern_nnum : p.lookup "intern_nnum" = some internNNum
  no_st8 : p.noSt8 = true

section nameSpec
variable (rom : List UInt8) (p : Prog) (hL : NameProg rom p)
include hL

/-- **`rom_name` computes its model** (any memory; the model says where it aborts). -/
theorem romName_specW (n : Nat) : ∀ (s₀ : St) (pos : Word),
    pcap s₀.mem < 2 ^ 63 ∧ s₀.mem.top.toNat < 2 ^ 41 →
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_name" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ romNameW rom n s₀.mem pos = some (r.headD 0, r.tail.headD 0, s'.mem); ⊤⦄ := by
  induction n with
  | zero =>
    intro s₀ pos _
    rw [invoke_eq _ hL.rom_name]; simp only [callFn, romName]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ pos hs
    have ih' := fun s₁ pos₁ h₁ => Triple.keep hL.no_st8 (ih s₁ pos₁ h₁)
    rw [invoke_eq _ hL.rom_name]
    simp only [callFn, romName]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ldc,
        internNAnon_spec p hL.nanon_find hL.nanon_push hL.intern_nanon n,
        internNStr_spec p hL.lit_hash hL.limbs_eq hL.nstr_match hL.nstr_find hL.nstr_push
          hL.intern_nstr n,
        internNNum_spec p hL.nnum_find hL.nnum_push hL.intern_nnum n,
        romU64_spec rom p hL.rom_u64 n, romPut_specW rom p hL.rom_put n, ih'] <;>
      finish [Keep.size, Keep.pcap]

end nameSpec

/-! ## `rom_name` refines `internName` -/

/-- The store tier's arrays (below 64, and their tier-1 twins `256‥319`) and `CTL` words (below
64): every intern writes only there. -/
def StoreA : List ArrId := lowTierArrs
def StoreC : List Word := (List.range 64).map UInt64.ofNat

theorem frame_store {A : List ArrId} {C : List Word} {m m' : Mem} (h : MemFrame A C m m')
    (hA : ∀ b ∈ A, b < 64 ∨ (256 ≤ b ∧ b < 320)) (hC : ∀ x ∈ C, x.toNat < 64) : MemFrame StoreA StoreC m m' :=
  h.mono (fun b hb => low_tier_mem b (hA b hb)) (fun x hx => by
    simp only [StoreC, List.mem_map, List.mem_range]
    exact ⟨x.toNat, hC x hx, by simp⟩)

theorem frame_grows {m m' : Mem} (h : Grows m m') : MemFrame StoreA StoreC m m' :=
  frame_store (grows_frame m m' h) (by intro b hb; simp only [List.mem_cons, List.not_mem_nil, or_false] at hb; rcases hb with rfl | rfl <;> decide) (by simp)

section nameRef
variable (rom : List UInt8) (hr : RomOK rom)
include hr

theorem romB_head (pos : Word) (b : UInt8) (bs rest : List UInt8) (h : rom.drop pos.toNat = (b :: bs) ++ rest) :
    romB rom pos = b.toUInt64 :=
  romB_of_drop rom pos (b :: bs) rest h 0 (by simp) pos (by simp)

theorem drop_pos (pos : Word) (bs rest : List UInt8) (h : rom.drop pos.toNat = bs ++ rest) (k : Nat)
    (hk : k ≤ bs.length) : (pos + UInt64.ofNat k).toNat = pos.toNat + k := by
  by_cases hb : bs.length = 0
  · have : k = 0 := by omega
    subst this; simp
  have := drop_len rom _ _ _ h (by omega)
  simp only [RomOK] at hr
  rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega

theorem drop_shift (pos : Word) (bs cs rest : List UInt8) (h : rom.drop pos.toNat = bs ++ cs ++ rest)
    (q : Word) (hq : q.toNat = pos.toNat + bs.length) : rom.drop q.toNat = cs ++ rest := by
  rw [hq, ← List.drop_drop, h, List.append_assoc, List.drop_left]

/-- **The model of `rom_name` refines `internName`**: from `ArenaD`, at the encoding of `x`. -/
theorem romNameW_ok (x : ConLeche.Name) (hx : nameFits x = true) :
    ∀ (n : Nat) (m : Mem) (a : AState) (pos : Word) (rest : List UInt8) (h q : Word) (m' : Mem),
    ArenaD m a → ModeOK m → rom.drop pos.toNat = encName x ++ rest → romNameW rom n m pos = some (h, q, m') →
    AM.ok (internName x) a ∧ ArenaD m' (AM.st (internName x) a) ∧ AM.res (internName x) a = decI h ∧
    h.toNat < 2 ^ 32 ∧ q.toNat = pos.toNat + (encName x).length ∧ MemFrame StoreA StoreC m m' := by
  induction x with
  | anonymous =>
    intro n m a pos rest h q m' hA hmo hd hW
    have h0 : romB rom pos = 0 := romB_head rom hr pos 0 [] rest hd
    cases n with
    | zero => simp [romNameW] at hW
    | succ n =>
    rw [romNameW_anon rom n m pos h0] at hW
    cases hI : nainternW m with
    | none => rw [hI] at hW; simp [nmAnonK] at hW
    | some r =>
    obtain ⟨w, m₁⟩ := r
    rw [hI] at hW
    simp only [nmAnonK] at hW
    split at hW
    · simp at hW
    rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨hok, hR, hres, hf⟩ := L.Front.nanon_A m a hA w m₁ hI
    refine ⟨hok, hR, hres, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, ?_,
      frame_store hf (by simp [tier1, tierOff, nanonSch, NAREC, NASLOT]) (by simp [nanonSch])⟩
    exact drop_pos rom hr pos (encName .anonymous) rest hd 1 (by simp [encName])
  | str pre str ih =>
    intro n m a pos rest h q m' hA hmo hd hW
    simp only [nameFits, Bool.and_eq_true, decide_eq_true_eq] at hx
    have h0 : romB rom pos = 1 := romB_head rom hr pos 1 _ rest hd
    cases n with
    | zero => simp [romNameW] at hW
    | succ n =>
    rw [romNameW_rec rom n m pos (by simp [h0])] at hW
    have hd1 : rom.drop (pos + 1).toNat = encName pre ++ (strB str ++ rest) := by
      have := drop_shift rom hr pos [1] (encName pre ++ strB str) rest (by simpa [encName] using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp [encName]))
      simpa using this
    cases hP : romNameW rom n m (pos + 1) with
    | none => rw [hP] at hW; simp [nmRecK] at hW
    | some r =>
    obtain ⟨h₁, q₁, m₁⟩ := r
    rw [hP, h0] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := ih hx.1 n m a (pos + 1) _ h₁ q₁ m₁ hA hmo hd1 hP
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp [encName])
    simp only [UInt64.ofNat_one] at hp1
    have hdq : rom.drop q₁.toNat = u64B str.toByteArray.size ++ (str.toByteArray.data.toList ++ rest) := by
      have := drop_shift rom hr (pos + 1) (encName pre) (strB str) rest (by rw [hd1, List.append_assoc])
        q₁ hq1
      rw [this, strB, List.append_assoc]
    rw [nmRecK_str rom _ _ _ _ rfl (u64OK_of_drop rom _ _ _ hdq hr)] at hW
    have hl := u64W_of_drop rom q₁ _ _ hdq (by omega) hr
    have hlen := drop_len rom _ _ _ hd (by simp [encName])
    simp only [encName, strB, List.length_cons, List.length_append] at hlen
    simp only [RomOK] at hr
    have hsz : str.toByteArray.data.toList.length = str.toByteArray.size := by simp
    have hq8 : (q₁ + 8).toNat = q₁.toNat + 8 := by
      rw [UInt64.toNat_add]; simp [u64B] at hlen ⊢; omega
    have hlN : (UInt64.ofNat str.toByteArray.size).toNat = str.toByteArray.size := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
    rw [hl] at hW
    simp only [romPutW] at hW
    by_cases hok : romPutOK rom m₁ (q₁ + 8) (UInt64.ofNat str.toByteArray.size)
    case neg => rw [ite_eq_right hok] at hW; simp [nmStrK] at hW
    rw [ite_eq_left hok] at hW
    simp only [nmStrK] at hW
    cases hI : nsinternW ((rputW rom m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) (q₁ + 8) (UInt64.ofNat str.toByteArray.size) 0).set64 CTL 0
        (m₁.top + UInt64.ofNat str.toByteArray.size)) h₁ m₁.top (UInt64.ofNat str.toByteArray.size) with
    | none => rw [hI] at hW; simp [nmStr2K] at hW
    | some r =>
    obtain ⟨w, m₃⟩ := r
    rw [hI] at hW
    simp only [nmStr2K] at hW
    split at hW
    · simp at hW
    rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨hg, hsl, hk, -⟩ := romPutW_facts rom m₁ (q₁ + 8) _ hR1.1.lit.1 hok (by simp [RomOK]; omega)
    have hR2 := ArenaD.grow _ _ hg _ hR1
    have hk' : sliceL (vpool ((rputW rom m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) (q₁ + 8) (UInt64.ofNat str.toByteArray.size) 0).set64 CTL 0
        (m₁.top + UInt64.ofNat str.toByteArray.size))) m₁.top.toNat
        (UInt64.ofNat str.toByteArray.size).toNat = strWords str := by
      rw [hk, hq8, hlN, ← List.drop_drop, hdq]
      simp [u64B, strWords]
    have hmo1 := (romNameW_topK hP).mode hA.1.lit.1 hmo
    have hmo2 := (romPut_topK rom hok).mode hR1.1.lit.1 hmo1
    obtain ⟨ok2, hR3, res2, hf2⟩ := L.Front.nstr_A _ _ hR2 w m₃ h₁ _ _ hlt1 hsl str hk' (ModeOK.slice0 hmo2 hsl) hI
    have hX : internName (.str pre str) = internName pre >>= fun hp => internNNode (.str hp str) := rfl
    have okX : AM.ok (internName (.str pre str)) a := by
      rw [hX, AM.ok_bind, res1]; exact ⟨ok1, ok2⟩
    refine ⟨okX, ?_, ?_, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, ?_, ?_⟩
    · rw [hX, AM.st_bind _ _ _ (hX ▸ okX), res1]; exact hR3
    · rw [hX, AM.res_bind _ _ _ ok1, res1]; exact res2
    · simp only [encName, strB, List.length_cons, List.length_append, hsz]
      rw [UInt64.toNat_add, hq8, hlN]; simp [u64B] at hlen ⊢; omega
    · exact (hf1.trans (frame_grows hg)).trans
        (frame_store hf2 (by simp [tier1, tierOff, nstrSch, NSREC, NSSLOT]) (by simp [nstrSch]))
  | num pre k ih =>
    intro n m a pos rest h q m' hA hmo hd hW
    simp only [nameFits, Bool.and_eq_true, decide_eq_true_eq] at hx
    have h0 : romB rom pos = 2 := romB_head rom hr pos 2 _ rest hd
    cases n with
    | zero => simp [romNameW] at hW
    | succ n =>
    rw [romNameW_rec rom n m pos (by simp [h0])] at hW
    have hd1 : rom.drop (pos + 1).toNat = encName pre ++ (u64B k ++ rest) := by
      have := drop_shift rom hr pos [2] (encName pre ++ u64B k) rest (by simpa [encName] using hd)
        (pos + 1) (drop_pos rom hr pos _ rest hd 1 (by simp [encName]))
      simpa using this
    cases hP : romNameW rom n m (pos + 1) with
    | none => rw [hP] at hW; simp [nmRecK] at hW
    | some r =>
    obtain ⟨h₁, q₁, m₁⟩ := r
    rw [hP, h0] at hW
    obtain ⟨ok1, hR1, res1, hlt1, hq1, hf1⟩ := ih hx.1 n m a (pos + 1) _ h₁ q₁ m₁ hA hmo hd1 hP
    have hdq : rom.drop q₁.toNat = u64B k ++ rest :=
      drop_shift rom hr (pos + 1) (encName pre) (u64B k) rest (by rw [hd1, List.append_assoc]) q₁ hq1
    rw [nmRecK_num rom _ _ _ _ rfl (u64OK_of_drop rom _ _ _ hdq hr)] at hW
    have hl := u64W_of_drop rom q₁ _ _ hdq hx.2 hr
    have hlen := drop_len rom _ _ _ hd (by simp [encName])
    have hp1 := drop_pos rom hr pos _ rest hd 1 (by simp [encName])
    simp only [UInt64.ofNat_one] at hp1
    simp only [encName, List.length_cons, List.length_append] at hlen
    simp only [RomOK] at hr
    rw [hl] at hW
    simp only [nmNumK] at hW
    cases hI : nninternW m₁ h₁ (UInt64.ofNat k) with
    | none => rw [hI] at hW; simp at hW
    | some r =>
    obtain ⟨w, m₃⟩ := r
    rw [hI] at hW
    simp only at hW
    split at hW
    · simp at hW
    rename_i hlt
    simp only [Option.some.injEq, Prod.mk.injEq] at hW
    obtain ⟨rfl, rfl, rfl⟩ := hW
    obtain ⟨ok2, hR3, res2, hf2⟩ := L.Front.nnum_A _ _ hR1 w m₃ h₁ _ hlt1 hI
    have hkN : (UInt64.ofNat k).toNat = k := by
      rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt hx.2
    rw [hkN] at ok2 hR3 res2
    have hX : internName (.num pre k) = internName pre >>= fun hp => internNNode (.num hp k) := rfl
    have okX : AM.ok (internName (.num pre k)) a := by
      rw [hX, AM.ok_bind, res1]; exact ⟨ok1, ok2⟩
    refine ⟨okX, ?_, ?_, by simp at hlt; exact UInt64.lt_iff_toNat_lt.mp hlt, ?_, ?_⟩
    · rw [hX, AM.st_bind _ _ _ (hX ▸ okX), res1]; exact hR3
    · rw [hX, AM.res_bind _ _ _ ok1, res1]; exact res2
    · simp only [encName, List.length_cons, List.length_append]
      rw [UInt64.toNat_add]; simp [u64B] at hlen ⊢; omega
    · exact hf1.trans (frame_store hf2 (by simp [tier1, tierOff, nnumSch, NNREC, NNSLOT]) (by simp [nnumSch]))

end nameRef

/-- **`rom_name` refines `internName`**: at a position where the ROM holds the encoding of `x`,
under `ArenaD`; it returns the handle and the position after the encoding, and writes only the
store tier. -/
@[refines ConRon.Arena.internName]
theorem romName_refines (rom : List UInt8) (p : Prog) (hL : NameProg rom p) (hr : RomOK rom)
    (x : ConLeche.Name) (hx : nameFits x = true) (n : Nat) (s₀ : St) (a₀ : AState) (pos : Word)
    (rest : List UInt8) (hA : ArenaD s₀.mem a₀) (hmo : ModeOK s₀.mem) (hd : rom.drop pos.toNat = encName x ++ rest) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "rom_name" [pos]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internName x) a₀ ∧ ArenaD s'.mem (AM.st (internName x) a₀) ∧
      AM.res (internName x) a₀ = decI (r.headD 0) ∧ (r.headD 0).toNat < 2 ^ 32 ∧
      (r.tail.headD 0).toNat = pos.toNat + (encName x).length ∧
      MemFrame StoreA StoreC s₀.mem s'.mem; ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hW⟩ := M.of_run (P := fun s => s = s₀) hs hrun
    (romName_specW rom p hL n s₀ pos ⟨hA.1.lit.1.2.2.1, hA.1.lit.1.top41⟩)
  subst hs
  exact ⟨hloc, romNameW_ok rom hr x hx n _ a₀ pos rest _ _ _ hA hmo hd hW⟩

/-- `ArenaD` across writes at or above array 64 and `CTL` word 64. -/
theorem ArenaD.frameHi {A : List ArrId} {C : List Word} {m m' : Mem} {a : AState}
    (hf : MemFrame A C m m') (hA : ∀ b ∈ A, 64 ≤ b ∧ b < 256) (hC : ∀ x ∈ C, 64 ≤ x.toNat) (h : ArenaD m a) :
    ArenaD m' a :=
  ⟨ArenaR.frame_ext A C hA hC m m' hf a h.1,
   DerR.frameM A C m m' hf (fun b hb => by
     have := hA b hb; simp only [ArrId] at this ⊢; omega) a h.2⟩

end L.Rom
