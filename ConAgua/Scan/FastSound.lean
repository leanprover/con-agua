module

public import ConAgua.Scan.Fast
public import ConAgua.Scan.Line
public import ConAgua.Front.FieldsExpr
import ConAgua.Scan.Common

@[expose] public section

/-!
# The fast path agrees with the generic scanner

On a line `fast_line` accepts (`Canon`, `ConAgua.Scan.Fast`), the generic scanner's models give
what the fast path returns: the validator `lineFwdN` accepts the line and ends where the fast path
ends, the line starts with its `{`, and the record passes (`recLineN`, `exprLineN`) give the fields
`fast_line` returns. `front_line`'s spec (`ConAgua.Front.Line`) then holds for its fast arm with the
model unchanged.

The walk over the models is per line shape (`appLine_sound`, …), built from steps proved once:
a canonical member `"K":v` (`nextMemberN_key`: the key's code, the value right after the colon),
a comma, a closing brace, and a canonical number (`NumAt.slot`, `NumAt.rd`).
-/

namespace L.Scan.FastSound

open L.Scan.Fast
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Values
open L.Scan.Leaves (skipWsN keyEndN numEndN)
open L.Scan.Key (keyAtN valueAtN)
open L.Scan.Line (lineFwdN lineLoopN lineN)

variable {b : Array UInt8}

/-! ## Bytes of a literal -/

theorem toNat_add_ofNat (p : Word) (j : Nat) (h : p.toNat + j < 2 ^ 64) :
    (p + UInt64.ofNat j).toNat = p.toNat + j := by
  rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]
  exact Nat.mod_eq_of_lt (by have : UInt64.size = 2 ^ 64 := rfl; omega)

theorem _root_.L.LitAt.get' {p : Word} {l : List UInt8} (h : LitAt b p l) (j : Nat)
    (hj : j < l.length) : p.toNat + j < b.size ∧ b.getD (p.toNat + j) 0 = l[j] := by
  have hf := h.fits
  have := h.get j hj
  refine ⟨by omega, ?_⟩
  rw [← this, getElem!_pos b _ (by omega)]
  simp [Array.getD, show p.toNat + j < b.size by omega]

theorem _root_.L.LitAt.bw {p : Word} {l : List UInt8} (h : LitAt b p l) (hb : b.size < 2 ^ 63) (j : Nat)
    (hj : j < l.length) : byteW b (p + UInt64.ofNat j) = (l[j]).toUInt64 := by
  obtain ⟨hk, he⟩ := h.get' j hj
  rw [byteW, toNat_add_ofNat p j (by omega), he]

theorem _root_.L.LitAt.bw0 {p : Word} {l : List UInt8} (h : LitAt b p l) (hb : b.size < 2 ^ 63)
    (hl : 0 < l.length) : byteW b p = (l[0]).toUInt64 := by
  have := h.bw hb 0 hl; simpa using this

theorem _root_.L.LitAt.take {p : Word} {l : List UInt8} (h : LitAt b p l) (m : Nat)
    (hm : m ≤ l.length) (l' : List UInt8) (hl' : l' = l.take m) : LitAt b p l' := by
  have hf := h.fits
  subst hl'
  refine ⟨by simp only [List.length_take]; omega, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take]
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take]
    exact h.get j (by simp at h2; omega)

theorem _root_.L.LitAt.sub {p : Word} {l : List UInt8} (h : LitAt b p l) (hb : b.size < 2 ^ 63) (k m : Nat)
    (hkm : k + m ≤ l.length) (l' : List UInt8) (hl' : l' = (l.drop k).take m) :
    LitAt b (p + UInt64.ofNat k) l' := by
  have hf := h.fits
  have hp : (p + UInt64.ofNat k).toNat = p.toNat + k := toNat_add_ofNat p k (by omega)
  subst hl'
  refine ⟨by simp only [hp, List.length_take, List.length_drop]; omega, ?_⟩
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_take, List.length_drop] <;> omega
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_take, List.getElem_drop, hp]
    rw [Nat.add_assoc]
    exact h.get (k + j) (by simp at h2; omega)

theorem toNat_add_one (p : Word) (h : p.toNat + 1 < 2 ^ 64) : (p + 1).toNat = p.toNat + 1 := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by simpa using h)

/-! ## A canonical member -/

theorem getD_of_lt {j : Nat} (h : j < b.size) : b.getD j 0 = b[j] := by simp [Array.getD, h]

theorem keyEndN_run (j k : Nat)
    (hd : ∀ t < k, j + t < b.size ∧ b.getD (j + t) 0 ≠ 34 ∧
      ¬ (b.getD (j + t) 0 < 32 ∨ b.getD (j + t) 0 = 92))
    (he : j + k < b.size ∧ b.getD (j + k) 0 = 34) : keyEndN b j = j + k := by
  induction k generalizing j with
  | zero =>
    obtain ⟨h, he⟩ := he
    simp only [Nat.add_zero] at h he ⊢
    rw [getD_of_lt h] at he
    exact L.Scan.Leaves.keyEndN_quote b j h he
  | succ k ih =>
    obtain ⟨h0, hq, hc⟩ := hd 0 (by omega)
    simp only [Nat.add_zero] at h0 hq hc
    rw [getD_of_lt h0] at hq hc
    rw [L.Scan.Leaves.keyEndN_other b j (j + 1) rfl h0 hq hc, ih (j + 1)]
    · omega
    · intro t ht
      have := hd (t + 1) (by omega)
      rwa [show j + (t + 1) = j + 1 + t by omega] at this
    · rwa [show j + (k + 1) = j + 1 + k by omega] at he

/-- JSON whitespace, as `skip_ws` tests it. -/
def IsWs (c : Word) : Prop := c = 32 ∨ c = 9 ∨ c = 13

instance (c : Word) : Decidable (IsWs c) := by unfold IsWs; infer_instance

theorem skipWsN_at (k : Nat) (hc : ¬ IsWs (byteW b (UInt64.ofNat k))) (hk : k < 2 ^ 64) :
    skipWsN b k = k := by
  by_cases h : k < b.size
  · apply L.Scan.Leaves.skipWsN_other b k h
    have hk' : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by
      have : UInt64.size = 2 ^ 64 := rfl; omega)
    simp only [IsWs, byteW, hk', Array.getD, h, dite_true] at hc
    intro h'; apply hc
    rcases h' with h' | h' | h' <;> simp [h']
  · exact L.Scan.Leaves.skipWsN_end b k (by omega)

/-- **A canonical member** `"K":v` at `q`: the key's code, its value right after the colon. -/
theorem nextMemberN_key (hb : b.size < 2 ^ 63) (q w : Word) (key : List UInt8) (hw : w ≠ 0)
    (hk : LitAt b q (34 :: key ++ [34, 58])) (hkc : ∀ c ∈ key, 32 ≤ c ∧ c ≠ 34 ∧ c ≠ 92)
    (hv : ¬ IsWs (byteW b (q + UInt64.ofNat (key.length + 3)))) :
    nextMemberN b q w =
      ⟨2, q, w, keyAtN b q (UInt64.ofNat key.length), q + UInt64.ofNat (key.length + 3)⟩ := by
  have hf := hk.fits
  simp only [List.length_append, List.length_cons, List.length_nil] at hf
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hq : q < UInt64.ofNat b.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]; omega
  have h0 : byteW b q = 34 := by
    have := hk.bw hb 0 (by simp); simpa using this
  rw [nextMemberN_quote b q w hq (by rw [h0]; decide) (by rw [h0]; decide) (by rw [h0]; decide) h0]
  have hke : keyEndN b (q + 1).toNat = q.toNat + 1 + key.length := by
    have hq1 : (q + 1).toNat = q.toNat + 1 := toNat_add_one q (by omega)
    rw [hq1]
    apply keyEndN_run
    · intro t ht
      obtain ⟨h1, h2⟩ := hk.get' (1 + t) (by simp; omega)
      have hkt := hkc key[t] (List.getElem_mem ht)
      rw [show q.toNat + (1 + t) = q.toNat + 1 + t by omega] at h1 h2
      refine ⟨h1, ?_⟩
      rw [h2]
      simp only [List.cons_append, Nat.add_comm 1 t, List.getElem_cons_succ,
        List.getElem_append_left ht]
      refine ⟨hkt.2.1, ?_⟩
      intro h; rcases h with h | h
      · exact absurd h (UInt8.not_lt.mpr hkt.1)
      · exact hkt.2.2 h
    · have hl : 1 + key.length < (34 :: key ++ [34, 58]).length := by simp; omega
      obtain ⟨h1, h2⟩ := hk.get' (1 + key.length) hl
      rw [show q.toNat + (1 + key.length) = q.toNat + 1 + key.length by omega] at h1 h2
      refine ⟨h1, ?_⟩
      rw [h2]
      simp [Nat.add_comm 1 key.length]
  have hkeW : UInt64.ofNat (keyEndN b (q + 1).toNat) = q + UInt64.ofNat (key.length + 1) := by
    rw [hke]; apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (by omega), toNat_add_ofNat q _ (by omega)]; omega
  have hcolon : byteW b (q + UInt64.ofNat (key.length + 2)) = 58 := by
    have hl : key.length + 2 < (34 :: key ++ [34, 58]).length := by simp
    have := hk.bw hb (key.length + 2) hl
    rw [this]; simp
  have hva : valueAtN b q (q + UInt64.ofNat (key.length + 1)) =
      q + UInt64.ofNat (key.length + 3) := by
    have e1 : (q + UInt64.ofNat (key.length + 1) + 1).toNat = q.toNat + (key.length + 2) := by
      rw [show q + UInt64.ofNat (key.length + 1) + 1 = q + UInt64.ofNat (key.length + 2) by
        rw [UInt64.add_assoc]; congr 1; apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by omega),
          UInt64.toNat_ofNat_of_lt' (by omega)]
        simp only [UInt64.toNat_one]; exact Nat.mod_eq_of_lt (by omega)]
      exact toNat_add_ofNat q _ (by omega)
    have hp : UInt64.ofNat (q.toNat + (key.length + 2)) = q + UInt64.ofNat (key.length + 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by omega), toNat_add_ofNat q _ (by omega)]
    have hlt : q + UInt64.ofNat (key.length + 2) < UInt64.ofNat b.size := by
      rw [UInt64.lt_iff_toNat_lt, toNat_add_ofNat q _ (by omega),
        UInt64.toNat_ofNat_of_lt' (by omega)]; omega
    have e2 : (q + UInt64.ofNat (key.length + 2) + 1).toNat = q.toNat + (key.length + 3) := by
      rw [toNat_add_one _ (by rw [toNat_add_ofNat q _ (by omega)]; omega),
        toNat_add_ofNat q _ (by omega)]; omega
    have hp3 : UInt64.ofNat (q.toNat + (key.length + 3)) = q + UInt64.ofNat (key.length + 3) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_ofNat_of_lt' (by omega), toNat_add_ofNat q _ (by omega)]
    unfold valueAtN
    simp only
    rw [e1, skipWsN_at _ (by rw [hp, hcolon]; simp [IsWs]) (by omega), hp,
      ite_eq_left ⟨hlt, hcolon⟩, e2, skipWsN_at _ (by rw [hp3]; exact hv) (by omega), hp3]
  have hne : q + UInt64.ofNat (key.length + 3) ≠ q := by
    intro h; have := congrArg UInt64.toNat h
    rw [toNat_add_ofNat q _ (by omega)] at this; omega
  have hkl : q + UInt64.ofNat (key.length + 1) - (q + 1) = UInt64.ofNat key.length := by
    apply UInt64.toNat_inj.mp
    have h1 := toNat_add_one q (by omega)
    rw [UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, toNat_add_ofNat q _ (by omega), h1]; omega),
      toNat_add_ofNat q _ (by omega), h1, UInt64.toNat_ofNat_of_lt' (by omega)]
    omega
  rw [hkeW, hva, hkl, ite_eq_right hw, ite_eq_right (by
    intro h; have := congrArg UInt64.toNat h
    rw [toNat_add_ofNat q _ (by omega)] at this; simp at this), ite_eq_right hne]

/-- A member at `q` with the key `key` (code `code`) and its value at `v`. -/
theorem nextMemberN_at (hb : b.size < 2 ^ 63) (q v w code : Word) (key : List UInt8) (hw : w ≠ 0)
    (hk : LitAt b q (34 :: key ++ [34, 58])) (hkc : ∀ c ∈ key, 32 ≤ c ∧ c ≠ 34 ∧ c ≠ 92)
    (hcode : keyAtN b q (UInt64.ofNat key.length) = code)
    (hv : q + UInt64.ofNat (key.length + 3) = v) (hvw : ¬ IsWs (byteW b v)) :
    nextMemberN b q w = ⟨2, q, w, code, v⟩ := by
  subst hv hcode; exact nextMemberN_key hb q w key hw hk hkc hvw

theorem lt_size_of_lit {p : Word} {l : List UInt8} (h : LitAt b p l) (hb : b.size < 2 ^ 63)
    (j : Nat) (hj : j < l.length) : p + UInt64.ofNat j < UInt64.ofNat b.size := by
  have := h.fits
  rw [UInt64.lt_iff_toNat_lt, toNat_add_ofNat p j (by omega),
    UInt64.toNat_ofNat_of_lt' (by have : UInt64.size = 2 ^ 64 := rfl; omega)]
  omega

/-- A comma at `q` (between members). -/
theorem nextMemberN_comma' (q : Word) (hq : q < UInt64.ofNat b.size) (h : byteW b q = 44) :
    nextMemberN b q 0 = nextMemberN b (q + 1) 1 := by
  rw [nextMemberN_comma b q 0 hq (by rw [h]; decide) (by rw [h]; decide) h]; rfl

/-- The closing brace at `q`. -/
theorem nextMemberN_close' (q w : Word) (hq : q < UInt64.ofNat b.size) (h : byteW b q = 125) :
    nextMemberN b q w = ⟨1, q, w, 0, 0⟩ :=
  nextMemberN_close b q w hq (by rw [h]; decide) h

/-! ## A canonical number -/

theorem _root_.L.Scan.Fast.NumAt.lt_size {v e x : Word} (h : NumAt b v e x) (hb : b.size < 2 ^ 63) :
    v.toNat < b.size ∧ e.toNat ≤ b.size ∧ v.toNat < e.toNat := by
  have := h.inb; have := UInt64.lt_iff_toNat_lt.mp h.lt; omega

theorem _root_.L.Scan.Fast.NumAt.slot {v e x : Word} (h : NumAt b v e x) (hb : b.size < 2 ^ 63) (ks : Word)
    (hks : ks < v) : slotNatN b ks v = e := by
  have he : UInt64.ofNat (numEndN b v.toNat) = e := by
    rw [h.endN]; exact UInt64.ofNat_toNat
  unfold slotNatN
  rw [he, ite_eq_right (Ne.symm (UInt64.ne_of_lt h.lt)),
    ite_eq_left (UInt64.lt_trans hks h.lt)]

theorem _root_.L.Scan.Fast.NumAt.rd {v e x : Word} (h : NumAt b v e x) (hb : b.size < 2 ^ 63) :
    L.Front.Fields.rdNatN b v e = x := by
  obtain ⟨h1, h2, h3⟩ := h.lt_size hb
  have := h.short
  unfold L.Front.Fields.rdNatN
  rw [ite_eq_right, h.val]
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  simp; omega

theorem _root_.L.Scan.Fast.NumAt.notWs {v e x : Word} (h : NumAt b v e x) : ¬ IsWs (byteW b v) := by
  have := h.first
  intro hw; rcases hw with hw | hw | hw <;> rw [hw] at this <;> revert this <;> decide

/-! ## The key codes -/

/-- A key's bytes as a member writes them: quote, key, quote, colon. -/
def keyLit (s : String) : List UInt8 := 34 :: bytesOf s ++ [34, 58]

theorem keyChars (s : String) (h : ((bytesOf s).all fun c => 32 ≤ c && c != 34 && c != 92) = true) :
    ∀ c ∈ bytesOf s, 32 ≤ c ∧ c ≠ 34 ∧ c ≠ 92 := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- A key's byte `j` (from `1`), as `key_at` reads it. -/
theorem keyByte {q : Word} {s : String} (h : LitAt b q (keyLit s)) (hb : b.size < 2 ^ 63) (j : Nat)
    (hj : j < (keyLit s).length) : byteW b (q + UInt64.ofNat j) = ((keyLit s)[j]).toUInt64 :=
  h.bw hb j hj

theorem key_app {q : Word} (h : LitAt b q (keyLit "app")) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (bytesOf "app").length) = 2 := by
  have h1 : byteW b (q + 1) = 97 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 112 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 112 := keyByte h hb 3 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, bytesOf]

theorem key_arg {q : Word} (h : LitAt b q (keyLit "arg")) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (bytesOf "arg").length) = 3 := by
  have h1 : byteW b (q + 1) = 97 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 114 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 103 := keyByte h hb 3 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, bytesOf]

theorem key_fn {q : Word} (h : LitAt b q (keyLit "fn")) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (bytesOf "fn").length) = 13 := by
  have h1 : byteW b (q + 1) = 102 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 110 := keyByte h hb 2 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, bytesOf]

theorem key_ie {q : Word} (h : LitAt b q (keyLit "ie")) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (bytesOf "ie").length) = 18 := by
  have h1 : byteW b (q + 1) = 105 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 101 := keyByte h hb 2 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG1N, h1, h2, bytesOf]

/-! ## Positions -/

theorem addc (x a c d : Word) (h : a + c = d) : x + a + c = x + d := by rw [UInt64.add_assoc, h]

theorem lt_add (x : Word) (k : Nat) (hk : 0 < k) (h : x.toNat + k < 2 ^ 64) :
    x < x + UInt64.ofNat k := by
  rw [UInt64.lt_iff_toNat_lt, toNat_add_ofNat x k h]; omega

/-! ## The line -/

/-- What the validator says about a line the fast path accepts: it scans, its record starts at
its first byte `{`, and the next line starts at `nx`. -/
structure LineOK (b : Array UInt8) (i nx : Word) : Prop where
  fwd : lineFwdN b i = (1, nx)
  ws : skipWsN b i.toNat = i.toNat
  lt : i < UInt64.ofNat b.size
  brace : byteW b i = 123

/-- The line's frame: `{` at `i`, the members from `i + 1` close at `c` (`lineLoopN`), and the
newline after the closing brace. -/
theorem lineOK_of (hb : b.size < 2 ^ 63) (i c : Word) (hi : i < UInt64.ofNat b.size)
    (h0 : byteW b i = 123) (hc : lineLoopN b (i + 1) = c + 1) (hic : i < c + 1)
    (hl : c + 1 < UInt64.ofNat b.size) (hn : byteW b (c + 1) = 10) :
    LineOK b i (c + 2) := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hiN := L.Scan.lt_of_lt_ofNat hi
  have hws : skipWsN b i.toNat = i.toNat :=
    skipWsN_at _ (by rw [UInt64.ofNat_toNat, h0]; simp [IsWs]) (by omega)
  refine ⟨?_, hws, hi, h0⟩
  have hcN := L.Scan.lt_of_lt_ofNat hl
  have hc0 : c + 1 ≠ 0 := by
    intro h; rw [h] at hic; exact UInt64.not_lt_zero hic
  unfold lineFwdN lineFwdN.lineFwd2N
  rw [hws, UInt64.ofNat_toNat, ite_eq_right (by rw [h0]; simp), ite_eq_right (by
    rw [UInt64.le_iff_toNat_le]; have := UInt64.lt_iff_toNat_lt.mp hi; omega),
    ite_eq_right (by rw [h0]; simp), hc, ite_eq_right hc0,
    skipWsN_at _ (by rw [UInt64.ofNat_toNat, hn]; simp [IsWs]) (by omega), UInt64.ofNat_toNat]
  unfold lineFwdN.lineEndN
  rw [ite_eq_left ⟨hl, hn⟩, addc c 1 1 2 (by decide)]

/-! ## App lines -/

theorem hApp_len : hApp.length = 8 := by decide
theorem kArg_len : kArg.length = 6 := by decide
theorem kFn_len : kFn.length = 6 := by decide
theorem kIe_len : kIe.length = 7 := by decide
theorem kEnd1_len : kEnd1.length = 2 := by decide

open L.Scan.Records (appN appBit appVal) in
open L.Front.Fields in
/-- **An app line** scans, and its fields are the expression record `(10, idx, f, a, a)`. -/
theorem appLine_sound (hb : b.size < 2 ^ 63) {i nx idx f a : Word} (h : AppLine b i nx idx f a) :
    LineOK b i nx ∧ (recLineN b (i + 1)).pl = 0 ∧ exprLineN b (i + 1) = ⟨10, idx, f, a, a⟩ := by
  obtain ⟨hhd, harg, hna, hfn, hnf, hie, hni, htl, hnx⟩ := h
  generalize (numR b (i + 8 + 6)).1 = e1 at *
  generalize (numR b (e1 + 6)).1 = e2 at *
  generalize (numR b (e2 + 7)).1 = e3 at *
  subst hnx
  have hs : UInt64.size = 2 ^ 64 := rfl
  have f0 := hhd.fits; have f2 := hfn.fits; have f3 := hie.fits; have f4 := htl.fits
  rw [hApp_len] at f0; rw [kFn_len] at f2; rw [kIe_len] at f3; rw [kEnd1_len] at f4
  obtain ⟨na1, na2, na3⟩ := hna.lt_size hb
  obtain ⟨nf1, nf2, nf3⟩ := hnf.lt_size hb
  obtain ⟨ni1, ni2, ni3⟩ := hni.lt_size hb
  have p14 : i + 8 + 6 = i + 14 := addc i 8 6 14 (by decide)
  rw [p14] at hna na1 na3
  have t14 : (i + 14).toNat = i.toNat + 14 := toNat_add_ofNat i 14 (by omega)
  have t8 : (i + 8).toNat = i.toNat + 8 := toNat_add_ofNat i 8 (by omega)
  have t1 : (e1 + 1).toNat = e1.toNat + 1 := toNat_add_ofNat e1 1 (by omega)
  have t6 : (e1 + 6).toNat = e1.toNat + 6 := toNat_add_ofNat e1 6 (by omega)
  have t21 : (e2 + 1).toNat = e2.toNat + 1 := toNat_add_ofNat e2 1 (by omega)
  have t22 : (e2 + 2).toNat = e2.toNat + 2 := toNat_add_ofNat e2 2 (by omega)
  have t27 : (e2 + 7).toNat = e2.toNat + 7 := toNat_add_ofNat e2 7 (by omega)
  have t31 : (e3 + 1).toNat = e3.toNat + 1 := toNat_add_ofNat e3 1 (by omega)
  -- the members
  have k1 : LitAt b (i + 1) (keyLit "app") := hhd.sub hb 1 6 (by decide) _ (by decide)
  have M1 : nextMemberN b (i + 1) 1 = ⟨2, i + 1, 1, 2, i + 7⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) k1 (keyChars _ (by decide)) (key_app k1 hb)
      (addc i 1 _ 7 (by decide)) (by
        rw [show i + 7 = i + UInt64.ofNat 7 from rfl, hhd.bw hb 7 (by decide)]; decide)
  have k2 : LitAt b (i + 8) (keyLit "arg") := harg.take 6 (by decide) _ (by decide)
  have M2 : nextMemberN b (i + 8) 1 = ⟨2, i + 8, 1, 3, i + 14⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) k2 (keyChars _ (by decide)) (key_arg k2 hb)
      (addc i 8 _ 14 (by decide)) hna.notWs
  have k3 : LitAt b (e1 + 1) (keyLit "fn") := hfn.sub hb 1 5 (by decide) _ (by decide)
  have M3 : nextMemberN b e1 0 = ⟨2, e1 + 1, 1, 13, e1 + 6⟩ := by
    rw [nextMemberN_comma' e1 (by simpa using lt_size_of_lit hfn hb 0 (by decide))
      ((hfn.bw0 hb (by decide)).trans (by decide))]
    exact nextMemberN_at hb _ _ _ _ _ (by decide) k3 (keyChars _ (by decide)) (key_fn k3 hb)
      (addc e1 1 _ 6 (by decide)) hnf.notWs
  have M4 : ∀ w, nextMemberN b e2 w = ⟨1, e2, w, 0, 0⟩ := fun w =>
    nextMemberN_close' e2 w (by simpa using lt_size_of_lit hie hb 0 (by decide))
      ((hie.bw0 hb (by decide)).trans (by decide))
  have k5 : LitAt b (e2 + 2) (keyLit "ie") := hie.sub hb 2 5 (by decide) _ (by decide)
  have M5 : nextMemberN b (e2 + 1) 0 = ⟨2, e2 + 2, 1, 18, e2 + 7⟩ := by
    rw [nextMemberN_comma' (e2 + 1) (lt_size_of_lit hie hb 1 (by decide))
      ((hie.bw hb 1 (by decide)).trans (by decide)), addc e2 1 1 2 (by decide)]
    exact nextMemberN_at hb _ _ _ _ _ (by decide) k5 (keyChars _ (by decide)) (key_ie k5 hb)
      (addc e2 2 _ 7 (by decide)) hni.notWs
  have M6 : ∀ w, nextMemberN b e3 w = ⟨1, e3, w, 0, 0⟩ := fun w =>
    nextMemberN_close' e3 w (by simpa using lt_size_of_lit htl hb 0 (by decide))
      ((htl.bw0 hb (by decide)).trans (by decide))
  -- the numbers
  have s1 : slotNatN b (i + 8) (i + 14) = e1 :=
    hna.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, t8, t14]; omega)
  have s2 : slotNatN b (e1 + 1) (e1 + 6) = e2 :=
    hnf.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, t1, t6]; omega)
  have s3 : slotNatN b (e2 + 2) (e2 + 7) = e3 :=
    hni.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, t22, t27]; omega)
  have t7 : (i + 7).toNat = i.toNat + 7 := toNat_add_ofNat i 7 (by omega)
  have t0 : (i + 1).toNat = i.toNat + 1 := toNat_add_ofNat i 1 (by omega)
  have hA : appN b (i + 7) = e2 + 1 := by
    unfold appN objEntryN
    rw [ite_eq_left ⟨by rw [UInt64.lt_iff_toNat_lt, t7, UInt64.toNat_ofNat_of_lt' (by omega)]; omega,
      (hhd.bw hb 7 (by decide)).trans (by decide)⟩, addc i 7 1 8 (by decide)]
    rw [objN_step _ _ _ b (i + 8) 1 0 e1 1 (by rw [M2]; simp) (by rw [M2]; simp)
      (by rw [M2]; simp [appBit]) (by rw [M2]; simp [appBit]) (by rw [M2]; simp [appVal, s1])
      (by rw [M2, UInt64.lt_iff_toNat_lt, t8]; omega) (by rw [M2]; simp [appBit])]
    rw [objN_step _ _ _ b e1 0 1 e2 3 (by rw [M3]; simp) (by rw [M3]; simp)
      (by rw [M3]; simp [appBit]) (by rw [M3]; simp [appBit]) (by rw [M3]; simp [appVal, s2])
      (by rw [M3, UInt64.lt_iff_toNat_lt, t1]; omega) (by rw [M3]; simp [appBit])]
    rw [objN_close _ _ _ b e2 0 3 (by rw [M4]), M4]
    simp
  have hS1 : L.Scan.Line.lineStepN b 2 (i + 1) (i + 7) 0 0 = (e2 + 1, 0, 3) := by
    rw [L.Scan.Line.lineStepN_pay b 2 _ _ _ _ (by decide) (by decide) (by decide),
      L.Scan.Line.lineKind_2, L.Scan.Line.lineVal_2, hA,
      ite_eq_left ⟨by decide, rfl, by rw [UInt64.lt_iff_toNat_lt, t0, t21]; omega⟩]
  have hS5 : L.Scan.Line.lineStepN b 18 (e2 + 2) (e2 + 7) 0 3 = (e3, 3, 3) := by
    rw [L.Scan.Line.lineStepN_idx b 18 _ _ _ _ (by decide), s3,
      ite_eq_left ⟨rfl, by rw [UInt64.lt_iff_toNat_lt, t22]; omega⟩]
    rfl
  have hL : lineLoopN b (i + 1) = e3 + 1 := by
    unfold lineLoopN
    rw [L.Scan.Line.lineN_step b _ _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only
    rw [hS1]
    simp only
    rw [ite_eq_right (by intro h; have := congrArg UInt64.toNat h; rw [t21] at this; simp at this)]
    rw [L.Scan.Line.lineN_step b _ _ _ _ (by rw [M5]; simp) (by rw [M5]; simp), M5]
    simp only
    rw [hS5]
    simp only
    rw [ite_eq_right (by intro h; rw [h] at ni3; simp at ni3)]
    rw [L.Scan.Line.lineN_close b _ _ _ _ (by rw [M6]), M6]
    simp
  refine ⟨lineOK_of hb i e3 (by simpa using lt_size_of_lit hhd hb 0 (by decide))
    ((hhd.bw0 hb (by decide)).trans (by decide)) hL
    (by rw [UInt64.lt_iff_toNat_lt, t31]; omega) (lt_size_of_lit htl hb 1 (by decide))
    ((htl.bw hb 1 (by decide)).trans (by decide)), ?_, ?_⟩
  · unfold recLineN
    rw [recN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp [Fld.none]
  · have r1 := hna.rd hb
    have r2 := hnf.rd hb
    have r3 := hni.rd hb
    have hO : recObjN b (i + 7) = ⟨e2 + 1, f, a, 0, 0⟩ := by
      unfold recObjN
      rw [addc i 7 1 8 (by decide), objRecN_key b _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
      simp only [exValN, numKey]
      simp only [show (3 : Word) ≠ 5 by decide, show (3 : Word) ≠ 37 by decide,
        show (3 : Word) ≠ 64 by decide, reduceIte, true_or, or_true, s1]
      rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t8]; omega), r1,
        objRecN_key b _ _ _ (by rw [M3]; simp) (by rw [M3]; simp), M3]
      simp only [exValN, numKey, show (13 : Word) ≠ 5 by decide, show (13 : Word) ≠ 37 by decide,
        show (13 : Word) ≠ 64 by decide, reduceIte, true_or, or_true, s2]
      rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t1]; omega), r2,
        objRecN_close b _ _ _ (by rw [M4]), M4]
      simp [objPut]
    have hE1 : exVN b 2 (i + 1) (i + 7) = ⟨e2 + 1, 10, f, a, a⟩ := by
      simp [exVN, hO, objFld]
    have hE5 : exVN b 18 (e2 + 2) (e2 + 7) = ⟨e3, 0, idx, 0, 0⟩ := by
      simp [exVN, s3, r3]
    unfold exprLineN
    rw [exprN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only
    rw [hE1]
    simp only
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t0, t21]; omega)]
    rw [exprN_key b _ _ _ (by rw [M5]; simp) (by rw [M5]; simp), M5]
    simp only
    rw [hE5]
    simp only
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t22]; omega),
      exprN_close b _ _ _ (by rw [M6])]
    simp [fldPut, Fld.none]

end L.Scan.FastSound
