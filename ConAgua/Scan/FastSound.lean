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
def keyLit (k : List UInt8) : List UInt8 := 34 :: k ++ [34, 58]

/-- The key `app`. -/
def yApp : List UInt8 := [97, 112, 112]
/-- The key `arg`. -/
def yArg : List UInt8 := [97, 114, 103]
/-- The key `fn`. -/
def yFn : List UInt8 := [102, 110]
/-- The key `ie`. -/
def yIe : List UInt8 := [105, 101]
/-- The key `lam`. -/
def yLam : List UInt8 := [108, 97, 109]
/-- The key `binderInfo`. -/
def yBinderInfo : List UInt8 := [98, 105, 110, 100, 101, 114, 73, 110, 102, 111]
/-- The key `body`. -/
def yBody : List UInt8 := [98, 111, 100, 121]
/-- The key `name`. -/
def yName : List UInt8 := [110, 97, 109, 101]
/-- The key `type`. -/
def yType : List UInt8 := [116, 121, 112, 101]
/-- The key `forallE`. -/
def yForallE : List UInt8 := [102, 111, 114, 97, 108, 108, 69]

theorem keyChars (k : List UInt8) (h : (k.all fun c => 32 ≤ c && c != 34 && c != 92) = true) :
    ∀ c ∈ k, 32 ≤ c ∧ c ≠ 34 ∧ c ≠ 92 := by
  intro c hc
  have := List.all_eq_true.mp h c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- A key's byte `j` (from `1`), as `key_at` reads it. -/
theorem keyByte {q : Word} {k : List UInt8} (h : LitAt b q (keyLit k)) (hb : b.size < 2 ^ 63) (j : Nat)
    (hj : j < (keyLit k).length) : byteW b (q + UInt64.ofNat j) = ((keyLit k)[j]).toUInt64 :=
  h.bw hb j hj

theorem key_app {q : Word} (h : LitAt b q (keyLit yApp)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (yApp).length) = 2 := by
  have h1 : byteW b (q + 1) = 97 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 112 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 112 := keyByte h hb 3 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, yApp]

theorem key_arg {q : Word} (h : LitAt b q (keyLit yArg)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (yArg).length) = 3 := by
  have h1 : byteW b (q + 1) = 97 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 114 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 103 := keyByte h hb 3 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, yArg]

theorem key_fn {q : Word} (h : LitAt b q (keyLit yFn)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (yFn).length) = 13 := by
  have h1 : byteW b (q + 1) = 102 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 110 := keyByte h hb 2 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, yFn]

theorem key_ie {q : Word} (h : LitAt b q (keyLit yIe)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat (yIe).length) = 18 := by
  have h1 : byteW b (q + 1) = 105 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 101 := keyByte h hb 2 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG1N, h1, h2, yIe]

theorem key_lam {q : Word} (h : LitAt b q (keyLit yLam)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat yLam.length) = 29 := by
  have h1 : byteW b (q + 1) = 108 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 97 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 109 := keyByte h hb 3 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG5N, h1, h2, h3, yLam]

theorem key_binderInfo {q : Word} (h : LitAt b q (keyLit yBinderInfo)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat yBinderInfo.length) = 5 := by
  have h1 : byteW b (q + 1) = 98 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 105 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 110 := keyByte h hb 3 (by decide)
  have h4 : byteW b (q + 4) = 100 := keyByte h hb 4 (by decide)
  have h5 : byteW b (q + 5) = 101 := keyByte h hb 5 (by decide)
  have h6 : byteW b (q + 6) = 114 := keyByte h hb 6 (by decide)
  have h7 : byteW b (q + 7) = 73 := keyByte h hb 7 (by decide)
  have h8 : byteW b (q + 8) = 110 := keyByte h hb 8 (by decide)
  have h9 : byteW b (q + 9) = 102 := keyByte h hb 9 (by decide)
  have h10 : byteW b (q + 10) = 111 := keyByte h hb 10 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, yBinderInfo]

theorem key_body {q : Word} (h : LitAt b q (keyLit yBody)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat yBody.length) = 6 := by
  have h1 : byteW b (q + 1) = 98 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 111 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 100 := keyByte h hb 3 (by decide)
  have h4 : byteW b (q + 4) = 121 := keyByte h hb 4 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, h4, yBody]

theorem key_name {q : Word} (h : LitAt b q (keyLit yName)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat yName.length) = 34 := by
  have h1 : byteW b (q + 1) = 110 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 97 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 109 := keyByte h hb 3 (by decide)
  have h4 : byteW b (q + 4) = 101 := keyByte h hb 4 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG2N, h1, h2, h3, h4, yName]

theorem key_type {q : Word} (h : LitAt b q (keyLit yType)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat yType.length) = 61 := by
  have h1 : byteW b (q + 1) = 116 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 121 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 112 := keyByte h hb 3 (by decide)
  have h4 : byteW b (q + 4) = 101 := keyByte h hb 4 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG3N, h1, h2, h3, h4, yType]

theorem key_forallE {q : Word} (h : LitAt b q (keyLit yForallE)) (hb : b.size < 2 ^ 63) :
    keyAtN b q (UInt64.ofNat yForallE.length) = 14 := by
  have h1 : byteW b (q + 1) = 102 := keyByte h hb 1 (by decide)
  have h2 : byteW b (q + 2) = 111 := keyByte h hb 2 (by decide)
  have h3 : byteW b (q + 3) = 114 := keyByte h hb 3 (by decide)
  have h4 : byteW b (q + 4) = 97 := keyByte h hb 4 (by decide)
  have h5 : byteW b (q + 5) = 108 := keyByte h hb 5 (by decide)
  have h6 : byteW b (q + 6) = 108 := keyByte h hb 6 (by decide)
  have h7 : byteW b (q + 7) = 69 := keyByte h hb 7 (by decide)
  simp [keyAtN, L.Scan.Key.keyAtG6N, h1, h2, h3, h4, h5, h6, h7, yForallE]

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
  have k1 : LitAt b (i + 1) (keyLit yApp) := hhd.sub hb 1 6 (by decide) _ (by decide)
  have M1 : nextMemberN b (i + 1) 1 = ⟨2, i + 1, 1, 2, i + 7⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) k1 (keyChars _ (by decide)) (key_app k1 hb)
      (addc i 1 _ 7 (by decide)) (by
        rw [show i + 7 = i + UInt64.ofNat 7 from rfl, hhd.bw hb 7 (by decide)]; decide)
  have k2 : LitAt b (i + 8) (keyLit yArg) := harg.take 6 (by decide) _ (by decide)
  have M2 : nextMemberN b (i + 8) 1 = ⟨2, i + 8, 1, 3, i + 14⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) k2 (keyChars _ (by decide)) (key_arg k2 hb)
      (addc i 8 _ 14 (by decide)) hna.notWs
  have k3 : LitAt b (e1 + 1) (keyLit yFn) := hfn.sub hb 1 5 (by decide) _ (by decide)
  have M3 : nextMemberN b e1 0 = ⟨2, e1 + 1, 1, 13, e1 + 6⟩ := by
    rw [nextMemberN_comma' e1 (by simpa using lt_size_of_lit hfn hb 0 (by decide))
      ((hfn.bw0 hb (by decide)).trans (by decide))]
    exact nextMemberN_at hb _ _ _ _ _ (by decide) k3 (keyChars _ (by decide)) (key_fn k3 hb)
      (addc e1 1 _ 6 (by decide)) hnf.notWs
  have M4 : ∀ w, nextMemberN b e2 w = ⟨1, e2, w, 0, 0⟩ := fun w =>
    nextMemberN_close' e2 w (by simpa using lt_size_of_lit hie hb 0 (by decide))
      ((hie.bw0 hb (by decide)).trans (by decide))
  have k5 : LitAt b (e2 + 2) (keyLit yIe) := hie.sub hb 2 5 (by decide) _ (by decide)
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

/-! ## Binder values -/

theorem _root_.L.LitAt.append {p : Word} {l₁ l₂ : List UInt8} (h₁ : LitAt b p l₁)
    (h₂ : LitAt b (p + UInt64.ofNat l₁.length) l₂) (hb : b.size < 2 ^ 63) :
    LitAt b p (l₁ ++ l₂) := by
  have f1 := h₁.fits; have f2 := h₂.fits
  have hp : (p + UInt64.ofNat l₁.length).toNat = p.toNat + l₁.length :=
    toNat_add_ofNat p _ (by omega)
  rw [hp] at f2
  refine ⟨by simp; omega, ?_⟩
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_map, List.getElem_range]
    by_cases hj : j < l₁.length
    · rw [List.getElem_append_left hj]; exact h₁.get j hj
    · rw [List.getElem_append_right (by omega)]
      have := h₂.get (j - l₁.length) (by simp at h1; omega)
      rw [hp, show p.toNat + l₁.length + (j - l₁.length) = p.toNat + j by omega] at this
      exact this

open L.Scan.Lit (matchLitN byteAtN) in
theorem matchLitN_iff (i : Nat) (W : List UInt8) (o n : Nat) : ∀ k,
    matchLitN b i W o n k = true ↔ ∀ t, k ≤ t → t < n → byteAtN b (i + t) = W.getD (o + t) 0 := by
  intro k
  induction h : n - k generalizing k with
  | zero =>
    rw [L.Scan.Lit.matchLitN_end b i W o n k (by omega)]
    exact ⟨fun _ t h1 h2 => absurd h2 (by omega), fun _ => rfl⟩
  | succ m ih =>
    rw [L.Scan.Lit.matchLitN]
    rw [ite_eq_left (show k < n by omega)]
    split
    · rw [ih (k + 1) (by omega)]
      constructor
      · intro h' t h1 h2
        by_cases ht : t = k
        · subst ht; assumption
        · exact h' t (by omega) h2
      · intro h' t h1 h2; exact h' t (by omega) h2
    · constructor
      · intro h'; cases h'
      · intro h'; exact absurd (h' k (Nat.le_refl _) (by omega)) ‹_›

open L.Scan.Lit (matchLitN byteAtN) in
/-- A literal match on bytes the line is known to have. -/
theorem matchLitN_lit {p : Word} {l : List UInt8} (h : LitAt b p l) (W : List UInt8) (o n : Nat)
    (hn : n ≤ l.length) (hall : ∀ t < n, l.getD t 0 = W.getD (o + t) 0) :
    matchLitN b p.toNat W o n 0 = true := by
  rw [matchLitN_iff]
  intro t _ h2
  obtain ⟨_, he⟩ := h.get' t (by omega)
  rw [byteAtN, he, ← hall t h2, ← List.getElem_eq_getD 0]

open L.Scan.Lit (matchLitN byteAtN) in
/-- A literal mismatch at a byte the line is known to have. -/
theorem matchLitN_miss_lit {p : Word} {l : List UInt8} (h : LitAt b p l) (W : List UInt8)
    (o n t : Nat) (ht : t < n) (htl : t < l.length) (hne : l.getD t 0 ≠ W.getD (o + t) 0) :
    matchLitN b p.toNat W o n 0 = false := by
  cases hm : matchLitN b p.toNat W o n 0 with
  | false => rfl
  | true =>
    exfalso
    have := (matchLitN_iff _ W o n 0).mp hm t (Nat.zero_le _) ht
    obtain ⟨_, he⟩ := h.get' t htl
    rw [byteAtN, he, List.getElem_eq_getD 0] at this
    exact hne this

theorem _root_.L.Scan.Fast.BiAt.toNat {p e : Word} (h : BiAt b p e) (hp : p.toNat + 15 < 2 ^ 64) :
    p.toNat + 8 ≤ e.toNat ∧ e.toNat ≤ p.toNat + 15 := by
  cases h <;> (rw [UInt64.toNat_add]; simp; omega)

/-- **A binder's value** after the quote at `v`: `scan_binder_info`'s end. -/
theorem binderInfoN_at (hb : b.size < 2 ^ 63) {v e : Word} (h : BiAt b (v + 1) e)
    (hq : byteW b v = 34) (hv : v.toNat < b.size) : binderInfoN b v = e := by
  have hs : UInt64.size = 2 ^ 64 := rfl
  have hlt : v < UInt64.ofNat b.size := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)]; exact hv
  unfold binderInfoN
  rw [ite_eq_left ⟨hlt, hq⟩]
  have m0 : ∀ {l : List UInt8}, LitAt b (v + 1) l → 0 < l.length → l.getD 0 0 ≠ 100 →
      ¬ L.Scan.Lit.matchLitN b (v + 1).toNat WORDS 0 8 0 = true := fun h hl hne => by
    rw [matchLitN_miss_lit h WORDS 0 8 0 (by decide) hl (by rw [show WORDS.getD (0 + 0) 0 = 100 from rfl]; exact hne)]; simp
  cases h with
  | dflt h1 =>
    rw [ite_eq_left (matchLitN_lit h1 WORDS 0 8 (by decide) (by decide))]
    exact (addc v 1 8 9 (by decide)).symm
  | impl h1 h2 =>
    have h12 := h1.append (show LitAt b (v + 1 + UInt64.ofNat biI8.length) kQ from h2) hb
    rw [ite_eq_right (m0 h12 (by decide) (by decide)),
      ite_eq_left (matchLitN_lit h12 WORDS 8 9 (by decide) (by decide))]
    exact (addc v 1 9 10 (by decide)).symm
  | inst h1 h2 =>
    have h12 := h1.append (show LitAt b (v + 1 + UInt64.ofNat biN8.length) biN5 from h2) hb
    have m1 : ¬ L.Scan.Lit.matchLitN b (v + 1).toNat WORDS 8 9 0 = true := by
      rw [matchLitN_miss_lit h12 WORDS 8 9 1 (by decide) (by decide) (by decide)]; simp
    have m2 : ¬ L.Scan.Lit.matchLitN b (v + 1).toNat WORDS 17 15 0 = true := by
      rw [matchLitN_miss_lit h12 WORDS 17 15 0 (by decide) (by decide) (by decide)]; simp
    rw [ite_eq_right (m0 h12 (by decide) (by decide)), ite_eq_right m1, ite_eq_right m2,
      ite_eq_left (matchLitN_lit h12 WORDS 32 13 (by decide) (by decide))]
    exact (addc v 1 13 14 (by decide)).symm
  | strict h1 h2 =>
    have h12 := h1.append (show LitAt b (v + 1 + UInt64.ofNat biS8.length) biS7 from h2) hb
    have m1 : ¬ L.Scan.Lit.matchLitN b (v + 1).toNat WORDS 8 9 0 = true := by
      rw [matchLitN_miss_lit h12 WORDS 8 9 0 (by decide) (by decide) (by decide)]; simp
    rw [ite_eq_right (m0 h12 (by decide) (by decide)), ite_eq_right m1,
      ite_eq_left (matchLitN_lit h12 WORDS 17 15 (by decide) (by decide))]
    exact (addc v 1 15 16 (by decide)).symm

/-- A comma, then a member with the key `key` (code `code`) and its value at `v`. -/
theorem nextMemberN_comma_at (hb : b.size < 2 ^ 63) (q v code : Word) (key : List UInt8)
    (hk : LitAt b q (44 :: keyLit key)) (hkc : ∀ c ∈ key, 32 ≤ c ∧ c ≠ 34 ∧ c ≠ 92)
    (hcode : LitAt b (q + 1) (keyLit key) → keyAtN b (q + 1) (UInt64.ofNat key.length) = code)
    (hv : q + 1 + UInt64.ofNat (key.length + 3) = v) (hvw : ¬ IsWs (byteW b v)) :
    nextMemberN b q 0 = ⟨2, q + 1, 1, code, v⟩ := by
  have h1 : LitAt b (q + 1) (keyLit key) :=
    hk.sub hb 1 (keyLit key).length (by simp only [List.length_cons]; omega) _ (by simp)
  rw [nextMemberN_comma' q (by simpa using lt_size_of_lit hk hb 0 (by simp))
    ((hk.bw0 hb (by simp)).trans (by simp))]
  exact nextMemberN_at hb _ _ _ _ key (by decide) h1 hkc (hcode h1) hv hvw

theorem kBody_eq : kBody = 44 :: keyLit yBody := by decide
theorem kName_eq : kName = 44 :: keyLit yName := by decide
theorem kType_eq : kType = 44 :: keyLit yType := by decide

open L.Scan.Records (binderN) in
open L.Front.Fields in
/-- What the generic models read from a binder object with its `{` at `v`, its `}` at `e`. -/
structure BndOK (b : Array UInt8) (v e bd t nm : Word) : Prop where
  scan : binderN b v = e + 1
  slots : recObjN b v = ⟨e + 1, t, bd, 0, nm⟩
  lt : v.toNat < e.toNat

open L.Scan.Records (binderN binderBit binderVal) in
open L.Front.Fields in
/-- **A binder object** with its `{` at `v` and its `}` at `bE4 b (v + 1)`: the validator ends after
it, and the record pass reads `type`, `body` and `name` into its slots. -/
theorem bndObj_sound (hb : b.size < 2 ^ 63) {v bd t : Word} (h : BndAt b (v + 1) bd t)
    (hv : v < UInt64.ofNat b.size) (h0 : byteW b v = 123)
    (hcl : bE4 b (v + 1) < UInt64.ofNat b.size) (hc : byteW b (bE4 b (v + 1)) = 125) :
    BndOK b v (bE4 b (v + 1)) bd t (numR b (bE2 b (v + 1) + 8)).2 := by
  obtain ⟨k1, k2, hbi, hbody, hnb, hname, hnn, htype, hnt⟩ := h
  generalize (numR b (bE2 b (v + 1) + 8)).2 = nm at *
  generalize bE4 b (v + 1) = e4 at *
  generalize bE3 b (v + 1) = e3 at *
  generalize bE2 b (v + 1) = e2 at *
  generalize bE1 b (v + 1) = e1 at *
  have hs : UInt64.size = 2 ^ 64 := rfl
  have f1 := k1.fits; have fb := hbody.fits; have fn := hname.fits; have ft := htype.fits
  simp only [show kBinderI.length = 8 from rfl, show kBody.length = 8 from rfl,
    show kName.length = 8 from rfl, show kType.length = 8 from rfl] at f1 fb fn ft
  obtain ⟨b1, b2, b3⟩ := hnb.lt_size hb
  obtain ⟨n1, n2, n3⟩ := hnn.lt_size hb
  obtain ⟨t1, t2, t3⟩ := hnt.lt_size hb
  have hvN := L.Scan.lt_of_lt_ofNat hv
  have hv1 : (v + 1).toNat = v.toNat + 1 := toNat_add_ofNat v 1 (by omega)
  have p14 : v + 1 + 8 + 6 = v + 14 + 1 := by
    rw [UInt64.add_assoc, UInt64.add_assoc, UInt64.add_assoc]; rfl
  rw [p14] at hbi
  -- the members
  have kbi : LitAt b (v + 1) (keyLit yBinderInfo) :=
    (k1.append (show LitAt b (v + 1 + UInt64.ofNat kBinderI.length) (kNfo.take 5) from
      k2.take 5 (by decide) _ rfl) hb).take 13 (by decide) _ (by decide)
  have q14 : byteW b (v + 14) = 34 := by
    have := k2.bw hb 5 (by decide)
    rw [show v + 1 + 8 + UInt64.ofNat 5 = v + 14 by rw [UInt64.add_assoc, UInt64.add_assoc]; rfl]
      at this
    exact this.trans (by decide)
  have t14 : (v + 14).toNat = v.toNat + 14 := toNat_add_ofNat v 14 (by omega)
  have M1 : nextMemberN b (v + 1) 1 = ⟨2, v + 1, 1, 5, v + 14⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) kbi (keyChars _ (by decide)) (key_binderInfo kbi hb)
      (addc v 1 _ 14 (by decide)) (by rw [q14]; decide)
  have h14 : (v + 14).toNat < b.size := by
    have := lt_size_of_lit k2 hb 5 (by decide)
    rw [show v + 1 + 8 + UInt64.ofNat 5 = v + 14 by rw [UInt64.add_assoc, UInt64.add_assoc]; rfl]
      at this
    exact L.Scan.lt_of_lt_ofNat this
  have hBI : binderInfoN b (v + 14) = e1 := binderInfoN_at hb hbi q14 h14
  have M2 : nextMemberN b e1 0 = ⟨2, e1 + 1, 1, 6, e1 + 8⟩ :=
    nextMemberN_comma_at hb _ _ _ _ (kBody_eq ▸ hbody) (keyChars _ (by decide))
      (fun h => key_body h hb)
      (addc e1 1 _ 8 (by decide)) hnb.notWs
  have M3 : nextMemberN b e2 0 = ⟨2, e2 + 1, 1, 34, e2 + 8⟩ :=
    nextMemberN_comma_at hb _ _ _ _ (kName_eq ▸ hname) (keyChars _ (by decide))
      (fun h => key_name h hb)
      (addc e2 1 _ 8 (by decide)) hnn.notWs
  have M4 : nextMemberN b e3 0 = ⟨2, e3 + 1, 1, 61, e3 + 8⟩ :=
    nextMemberN_comma_at hb _ _ _ _ (kType_eq ▸ htype) (keyChars _ (by decide))
      (fun h => key_type h hb)
      (addc e3 1 _ 8 (by decide)) hnt.notWs
  have M5 : ∀ w, nextMemberN b e4 w = ⟨1, e4, w, 0, 0⟩ := fun w => nextMemberN_close' e4 w hcl hc
  -- the numbers
  have te1 : (e1 + 1).toNat = e1.toNat + 1 := toNat_add_ofNat e1 1 (by omega)
  have te8 : (e1 + 8).toNat = e1.toNat + 8 := toNat_add_ofNat e1 8 (by omega)
  have te21 : (e2 + 1).toNat = e2.toNat + 1 := toNat_add_ofNat e2 1 (by omega)
  have te28 : (e2 + 8).toNat = e2.toNat + 8 := toNat_add_ofNat e2 8 (by omega)
  have te31 : (e3 + 1).toNat = e3.toNat + 1 := toNat_add_ofNat e3 1 (by omega)
  have te38 : (e3 + 8).toNat = e3.toNat + 8 := toNat_add_ofNat e3 8 (by omega)
  have s2 : slotNatN b (e1 + 1) (e1 + 8) = e2 :=
    hnb.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, te1, te8]; omega)
  have s3 : slotNatN b (e2 + 1) (e2 + 8) = e3 :=
    hnn.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, te21, te28]; omega)
  have s4 : slotNatN b (e3 + 1) (e3 + 8) = e4 :=
    hnt.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, te31, te38]; omega)
  have l1 : v + 1 < e1 := by
    have t15 : (v + 14 + 1).toNat = v.toNat + 15 := by
      rw [toNat_add_one _ (by omega), t14]
    have := hbi.toNat (by omega)
    rw [UInt64.lt_iff_toNat_lt, hv1]; omega
  have rb := hnb.rd hb
  have rn := hnn.rd hb
  have rt := hnt.rd hb
  refine ⟨?_, ?_, ?_⟩
  · unfold binderN objEntryN
    rw [ite_eq_left ⟨hv, h0⟩]
    rw [objN_step _ _ _ b (v + 1) 1 0 e1 1 (by rw [M1]; simp) (by rw [M1]; simp)
      (by rw [M1]; simp [binderBit]) (by rw [M1]; simp [binderBit])
      (by rw [M1]; simp [binderVal, hBI]) (by rw [M1]; exact l1) (by rw [M1]; simp [binderBit])]
    rw [objN_step _ _ _ b e1 0 1 e2 3 (by rw [M2]; simp) (by rw [M2]; simp)
      (by rw [M2]; simp [binderBit]) (by rw [M2]; simp [binderBit])
      (by rw [M2]; simp [binderVal, s2]) (by rw [M2, UInt64.lt_iff_toNat_lt, te1]; omega)
      (by rw [M2]; simp [binderBit])]
    rw [objN_step _ _ _ b e2 0 3 e3 7 (by rw [M3]; simp) (by rw [M3]; simp)
      (by rw [M3]; simp [binderBit]) (by rw [M3]; simp [binderBit])
      (by rw [M3]; simp [binderVal, s3]) (by rw [M3, UInt64.lt_iff_toNat_lt, te21]; omega)
      (by rw [M3]; simp [binderBit])]
    rw [objN_step _ _ _ b e3 0 7 e4 15 (by rw [M4]; simp) (by rw [M4]; simp)
      (by rw [M4]; simp [binderBit]) (by rw [M4]; simp [binderBit])
      (by rw [M4]; simp [binderVal, s4]) (by rw [M4, UInt64.lt_iff_toNat_lt, te31]; omega)
      (by rw [M4]; simp [binderBit])]
    rw [objN_close _ _ _ b e4 0 15 (by rw [M5]), M5]
    simp
  · unfold recObjN
    rw [objRecN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only [exValN, reduceIte, hBI]
    rw [ite_eq_left l1, objRecN_key b _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
    simp only [exValN, numKey, show (6 : Word) ≠ 5 by decide, show (6 : Word) ≠ 37 by decide,
      show (6 : Word) ≠ 64 by decide, reduceIte, true_or, or_true, s2]
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, te1]; omega), rb,
      objRecN_key b _ _ _ (by rw [M3]; simp) (by rw [M3]; simp), M3]
    simp only [exValN, numKey, show (34 : Word) ≠ 5 by decide, show (34 : Word) ≠ 37 by decide,
      show (34 : Word) ≠ 64 by decide, reduceIte, true_or, or_true, s3]
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, te21]; omega), rn,
      objRecN_key b _ _ _ (by rw [M4]; simp) (by rw [M4]; simp), M4]
    simp only [exValN, numKey, show (61 : Word) ≠ 5 by decide, show (61 : Word) ≠ 37 by decide,
      show (61 : Word) ≠ 64 by decide, reduceIte, true_or, or_true, s4]
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, te31]; omega), rt,
      objRecN_close b _ _ _ (by rw [M5]), M5]
    simp [objPut]
  · have t15 : (v + 14 + 1).toNat = v.toNat + 15 := by
      rw [toNat_add_one _ (by omega), t14]
    have := hbi.toNat (by omega)
    omega

/-! ## Lambda and pi lines -/

open L.Scan.Records (binderN) in
open L.Front.Fields in
/-- **A lambda line** scans, and its fields are the expression record `(11, idx, t, bd, bd)`. -/
theorem lamLine_sound (hb : b.size < 2 ^ 63) {i nx idx t bd : Word}
    (h : LamLine b i nx idx t bd) :
    LineOK b i nx ∧ (recLineN b (i + 1)).pl = 0 ∧ exprLineN b (i + 1) = ⟨11, idx, t, bd, bd⟩ := by
  obtain ⟨hhd, hni, hlam, hbnd, htl, hnx⟩ := h
  generalize (numR b (i + 6)).1 = e0 at *
  have hs : UInt64.size = 2 ^ 64 := rfl
  have f0 := hhd.fits; have fl := hlam.fits; have ft := htl.fits
  simp only [show hIe.length = 6 from rfl, show kLam.length = 8 from rfl,
    show kEnd2.length = 3 from rfl] at f0 fl ft
  obtain ⟨ni1, ni2, ni3⟩ := hni.lt_size hb
  have p8 : e0 + 8 = e0 + 7 + 1 := (addc e0 7 1 8 (by decide)).symm
  rw [p8] at hbnd htl hnx
  have t0 : (e0 + 7).toNat = e0.toNat + 7 := toNat_add_ofNat e0 7 (by omega)
  have q7 : byteW b (e0 + 7) = 123 := (hlam.bw hb 7 (by decide)).trans (by decide)
  have h4lt : bE4 b (e0 + 7 + 1) < UInt64.ofNat b.size := by simpa using lt_size_of_lit htl hb 0 (by decide)
  have h4c : byteW b (bE4 b (e0 + 7 + 1)) = 125 := (htl.bw0 hb (by decide)).trans (by decide)
  obtain ⟨hB, hO, hlt4⟩ := bndObj_sound hb hbnd (by
    rw [UInt64.lt_iff_toNat_lt, t0, UInt64.toNat_ofNat_of_lt' (by omega)]; omega) q7 h4lt h4c
  generalize bE4 b (e0 + 7 + 1) = e4 at *
  generalize (numR b (bE2 b (e0 + 7 + 1) + 8)).2 = nm at *
  subst hnx
  have f4 := L.Scan.lt_of_lt_ofNat h4lt
  have t6 : (i + 6).toNat = i.toNat + 6 := toNat_add_ofNat i 6 (by omega)
  have t1 : (i + 1).toNat = i.toNat + 1 := toNat_add_ofNat i 1 (by omega)
  have te1 : (e0 + 1).toNat = e0.toNat + 1 := toNat_add_ofNat e0 1 (by omega)
  have t41 : (e4 + 1).toNat = e4.toNat + 1 := toNat_add_ofNat e4 1 (by omega)
  -- the members
  have k1 : LitAt b (i + 1) (keyLit yIe) := hhd.sub hb 1 5 (by decide) _ (by decide)
  have M1 : nextMemberN b (i + 1) 1 = ⟨2, i + 1, 1, 18, i + 6⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) k1 (keyChars _ (by decide)) (key_ie k1 hb)
      (addc i 1 _ 6 (by decide)) hni.notWs
  have M2 : nextMemberN b e0 0 = ⟨2, e0 + 1, 1, 29, e0 + 7⟩ :=
    nextMemberN_comma_at hb _ _ _ _ (hlam.take 7 (by decide) _ (by decide))
      (keyChars _ (by decide)) (fun h => key_lam h hb) (addc e0 1 _ 7 (by decide))
      (by rw [q7]; decide)
  have M3 : ∀ w, nextMemberN b (e4 + 1) w = ⟨1, e4 + 1, w, 0, 0⟩ := fun w =>
    nextMemberN_close' _ w (lt_size_of_lit htl hb 1 (by decide))
      ((htl.bw hb 1 (by decide)).trans (by decide))
  rw [t6] at ni1 ni3
  have s0 : slotNatN b (i + 1) (i + 6) = e0 :=
    hni.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, t1, t6]; omega)
  have hS1 : L.Scan.Line.lineStepN b 18 (i + 1) (i + 6) 0 0 = (e0, 3, 0) := by
    rw [L.Scan.Line.lineStepN_idx b 18 _ _ _ _ (by decide), s0,
      ite_eq_left ⟨rfl, by rw [UInt64.lt_iff_toNat_lt, t1]; omega⟩]
    rfl
  have hS2 : L.Scan.Line.lineStepN b 29 (e0 + 1) (e0 + 7) 3 0 = (e4 + 1, 3, 3) := by
    rw [L.Scan.Line.lineStepN_pay b 29 _ _ _ _ (by decide) (by decide) (by decide),
      L.Scan.Line.lineKind_29, L.Scan.Line.lineVal_29, hB,
      ite_eq_left ⟨by decide, rfl, by rw [UInt64.lt_iff_toNat_lt, te1, t41]; omega⟩]
  have hL : lineLoopN b (i + 1) = e4 + 1 + 1 := by
    unfold lineLoopN
    rw [L.Scan.Line.lineN_step b _ _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only
    rw [hS1]
    simp only
    rw [ite_eq_right (by intro h; rw [h] at ni3; simp at ni3)]
    rw [L.Scan.Line.lineN_step b _ _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
    simp only
    rw [hS2]
    simp only
    rw [ite_eq_right (by intro h; have := congrArg UInt64.toNat h; rw [t41] at this; simp at this)]
    rw [L.Scan.Line.lineN_close b _ _ _ _ (by rw [M3]), M3]
    simp
  have e43 : e4 + 3 = e4 + 1 + 2 := (addc e4 1 2 3 (by decide)).symm
  have e42 : e4 + 1 + 1 = e4 + 2 := addc e4 1 1 2 (by decide)
  refine ⟨e43 ▸ lineOK_of hb i (e4 + 1) (by simpa using lt_size_of_lit hhd hb 0 (by decide))
    ((hhd.bw0 hb (by decide)).trans (by decide)) hL
    (by rw [UInt64.lt_iff_toNat_lt, toNat_add_one _ (by omega), t41]; omega)
    (by rw [e42]; exact lt_size_of_lit htl hb 2 (by decide))
    (by rw [e42]; exact (htl.bw hb 2 (by decide)).trans (by decide)), ?_, ?_⟩
  · unfold recLineN
    rw [recN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only [show (18 : Word) = 21 ∨ (18 : Word) = 19 ∨ (18 : Word) = 18 by decide, reduceIte,
      or_true]
    rw [s0, ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t1]; omega),
      recN_key b _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
    simp [Fld.none]
  · have r0 := hni.rd hb
    have hE1 : exVN b 18 (i + 1) (i + 6) = ⟨e0, 0, idx, 0, 0⟩ := by simp [exVN, s0, r0]
    have hE2 : exVN b 29 (e0 + 1) (e0 + 7) = ⟨e4 + 1, 11, t, bd, bd⟩ := by
      simp [exVN, hO, objFld]
    unfold exprLineN
    rw [exprN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only
    rw [hE1]
    simp only
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t1]; omega)]
    rw [exprN_key b _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
    simp only
    rw [hE2]
    simp only
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, te1, t41]; omega),
      exprN_close b _ _ _ (by rw [M3])]
    simp [fldPut, Fld.none]

open L.Scan.Records (binderN) in
open L.Front.Fields in
/-- **A pi line** scans, and its fields are the expression record `(12, idx, t, bd, bd)`. -/
theorem forallLine_sound (hb : b.size < 2 ^ 63) {i nx idx t bd : Word}
    (h : ForallLine b i nx idx t bd) :
    LineOK b i nx ∧ (recLineN b (i + 1)).pl = 0 ∧ exprLineN b (i + 1) = ⟨12, idx, t, bd, bd⟩ := by
  obtain ⟨hhd, hk, hbnd, hie, hni, htl, hnx⟩ := h
  have hs : UInt64.size = 2 ^ 64 := rfl
  have f0 := hhd.fits; have fk := hk.fits
  simp only [show hForall.length = 8 from rfl, show kForallE.length = 4 from rfl] at f0 fk
  have p12 : i + 8 + 4 = i + 11 + 1 := by
    rw [UInt64.add_assoc, UInt64.add_assoc]; rfl
  rw [p12] at hbnd hie hni htl hnx
  have t8 : (i + 8).toNat = i.toNat + 8 := toNat_add_ofNat i 8 (by omega)
  have t11 : (i + 11).toNat = i.toNat + 11 := toNat_add_ofNat i 11 (by omega)
  have q11 : byteW b (i + 11) = 123 := by
    have := hk.bw hb 3 (by decide)
    rw [show i + 8 + UInt64.ofNat 3 = i + 11 by rw [UInt64.add_assoc]; rfl] at this
    exact this.trans (by decide)
  have h4lt : bE4 b (i + 11 + 1) < UInt64.ofNat b.size := by
    simpa using lt_size_of_lit hie hb 0 (by decide)
  have h4c : byteW b (bE4 b (i + 11 + 1)) = 125 := (hie.bw0 hb (by decide)).trans (by decide)
  obtain ⟨hB, hO, hlt4⟩ := bndObj_sound hb hbnd (by
    rw [UInt64.lt_iff_toNat_lt, t11, UInt64.toNat_ofNat_of_lt' (by omega)]; omega) q11 h4lt h4c
  generalize bE4 b (i + 11 + 1) = e4 at *
  generalize (numR b (bE2 b (i + 11 + 1) + 8)).2 = nm at *
  generalize (numR b (e4 + 7)).1 = e5 at *
  subst hnx
  have f4 := L.Scan.lt_of_lt_ofNat h4lt
  have f3 := hie.fits; have f5 := htl.fits
  simp only [show kIe.length = 7 from rfl, show kEnd1.length = 2 from rfl] at f3 f5
  obtain ⟨ni1, ni2, ni3⟩ := hni.lt_size hb
  have t1 : (i + 1).toNat = i.toNat + 1 := toNat_add_ofNat i 1 (by omega)
  have t41 : (e4 + 1).toNat = e4.toNat + 1 := toNat_add_ofNat e4 1 (by omega)
  have t42 : (e4 + 2).toNat = e4.toNat + 2 := toNat_add_ofNat e4 2 (by omega)
  have t47 : (e4 + 7).toNat = e4.toNat + 7 := toNat_add_ofNat e4 7 (by omega)
  have t51 : (e5 + 1).toNat = e5.toNat + 1 := toNat_add_ofNat e5 1 (by omega)
  rw [t47] at ni1 ni3
  -- the members
  have k1 : LitAt b (i + 1) (keyLit yForallE) :=
    ((hhd.sub hb 1 7 (by decide) _ rfl).append (show LitAt b (i + 1 + UInt64.ofNat 7)
      (kForallE.take 3) by
        rw [show i + 1 + UInt64.ofNat 7 = i + 8 by rw [UInt64.add_assoc]; rfl]
        exact hk.take 3 (by decide) _ rfl) hb).take 10 (by decide) _ (by decide)
  have M1 : nextMemberN b (i + 1) 1 = ⟨2, i + 1, 1, 14, i + 11⟩ :=
    nextMemberN_at hb _ _ _ _ _ (by decide) k1 (keyChars _ (by decide)) (key_forallE k1 hb)
      (addc i 1 _ 11 (by decide)) (by rw [q11]; decide)
  have k2 : LitAt b (e4 + 1) (44 :: keyLit yIe) := hie.sub hb 1 6 (by decide) _ (by decide)
  have M2 : nextMemberN b (e4 + 1) 0 = ⟨2, e4 + 1 + 1, 1, 18, e4 + 7⟩ :=
    nextMemberN_comma_at hb _ _ _ _ k2 (keyChars _ (by decide)) (fun h => key_ie h hb)
      (by rw [UInt64.add_assoc, UInt64.add_assoc]; rfl) hni.notWs
  have e42 : e4 + 1 + 1 = e4 + 2 := addc e4 1 1 2 (by decide)
  rw [e42] at M2
  have M3 : ∀ w, nextMemberN b e5 w = ⟨1, e5, w, 0, 0⟩ := fun w =>
    nextMemberN_close' _ w (by simpa using lt_size_of_lit htl hb 0 (by decide))
      ((htl.bw0 hb (by decide)).trans (by decide))
  have s5 : slotNatN b (e4 + 2) (e4 + 7) = e5 :=
    hni.slot hb _ (by rw [UInt64.lt_iff_toNat_lt, t42, t47]; omega)
  have hS1 : L.Scan.Line.lineStepN b 14 (i + 1) (i + 11) 0 0 = (e4 + 1, 0, 3) := by
    rw [L.Scan.Line.lineStepN_pay b 14 _ _ _ _ (by decide) (by decide) (by decide),
      L.Scan.Line.lineKind_14, L.Scan.Line.lineVal_14, hB,
      ite_eq_left ⟨by decide, rfl, by rw [UInt64.lt_iff_toNat_lt, t1, t41]; omega⟩]
  have hS2 : L.Scan.Line.lineStepN b 18 (e4 + 2) (e4 + 7) 0 3 = (e5, 3, 3) := by
    rw [L.Scan.Line.lineStepN_idx b 18 _ _ _ _ (by decide), s5,
      ite_eq_left ⟨rfl, by rw [UInt64.lt_iff_toNat_lt, t42]; omega⟩]
    rfl
  have hL : lineLoopN b (i + 1) = e5 + 1 := by
    unfold lineLoopN
    rw [L.Scan.Line.lineN_step b _ _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only
    rw [hS1]
    simp only
    rw [ite_eq_right (by intro h; have := congrArg UInt64.toNat h; rw [t41] at this; simp at this)]
    rw [L.Scan.Line.lineN_step b _ _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
    simp only
    rw [hS2]
    simp only
    rw [ite_eq_right (by intro h; rw [h] at ni3; simp at ni3)]
    rw [L.Scan.Line.lineN_close b _ _ _ _ (by rw [M3]), M3]
    simp
  refine ⟨lineOK_of hb i e5 (by simpa using lt_size_of_lit hhd hb 0 (by decide))
    ((hhd.bw0 hb (by decide)).trans (by decide)) hL
    (by rw [UInt64.lt_iff_toNat_lt, t51]; omega) (lt_size_of_lit htl hb 1 (by decide))
    ((htl.bw hb 1 (by decide)).trans (by decide)), ?_, ?_⟩
  · unfold recLineN
    rw [recN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp [Fld.none]
  · have r5 := hni.rd hb
    have hE1 : exVN b 14 (i + 1) (i + 11) = ⟨e4 + 1, 12, t, bd, bd⟩ := by
      simp [exVN, hO, objFld]
    have hE2 : exVN b 18 (e4 + 2) (e4 + 7) = ⟨e5, 0, idx, 0, 0⟩ := by simp [exVN, s5, r5]
    unfold exprLineN
    rw [exprN_key b _ _ _ (by rw [M1]; simp) (by rw [M1]; simp), M1]
    simp only
    rw [hE1]
    simp only
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t1, t41]; omega)]
    rw [exprN_key b _ _ _ (by rw [M2]; simp) (by rw [M2]; simp), M2]
    simp only
    rw [hE2]
    simp only
    rw [ite_eq_left (by rw [UInt64.lt_iff_toNat_lt, t42]; omega), exprN_close b _ _ _ (by rw [M3])]
    simp [fldPut, Fld.none]

end L.Scan.FastSound
