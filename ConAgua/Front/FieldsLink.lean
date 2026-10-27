module

public import ConAgua.Front.Fields
public import ConAgua.Scan.RecordsLink
import ConAgua.Scan.LeafLink
import ConAgua.Scan.LineLink
import ConAgua.Scan.Link
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section
set_option linter.unusedSectionVars false


/-!
# The fields of name and level lines, linked to con-leche

On a line con-leche's scanner accepts, `rec_line_loop`'s words are the fields of the record it
returns (`recLine_link`). Each loop of `ConAgua.Front.Fields` is related to con-leche's on its
`ok` path only: the validator (`ConAgua.Scan.LineLink`) has already decided that the line scans,
so the error branches of con-leche's loops are discharged by their result, and the second pass
needs none of the checks.

A number is related by `ItemR x n` ("`x` is `n` unless it is `NONE`"), a string body `[vs, ve)`
by `StrR` (con-leche's `scanString` reads the string there).
-/

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Front.Fields

/-- The word `x` read for the number `n`: it is `n`, unless the number was too long. -/
def ItemR (x : Word) (n : Nat) : Prop := x ≠ NONE → x.toNat = n

theorem itemR_none (n : Nat) : ItemR NONE n := fun h => absurd rfl h

theorem itemR_zero : ItemR 0 0 := fun _ => rfl

/-- The bytes `[lo, hi)` hold no backslash. -/
def NoEsc (b : ByteArray) (lo hi : Nat) : Prop := ∀ j, lo ≤ j → j < hi → b.data.getD j 0 ≠ 92

/-- The string body `[vs, ve)` is `s`, if it has no escape. -/
def StrOK (b : ByteArray) (vs ve : Word) (s : String) : Prop :=
  NoEsc b vs.toNat ve.toNat → String.fromUTF8? (b.extract vs.toNat ve.toNat) = some s

/-- A string's body `[c, d)`: con-leche's `scanString` at the opening quote `v` reads `s` and
ends at `e`, after the closing quote. -/
def StrR (b : ByteArray) (c d : Word) (s : String) : Prop :=
  ∃ v e : USize, v.toUInt64 + 1 = c ∧ e.toUInt64 - 1 = d ∧ ConLeche.Frontend.scanString b v = .ok s e

theorem getD_rev_cons (acc : List Nat) (x : Nat) (k : Nat) (hk : k < acc.length) :
    (x :: acc).reverse.getD k 0 = acc.reverse.getD k 0 := by
  simp only [List.reverse_cons, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simpa using hk)]

theorem getD_rev_cons_self (acc : List Nat) (x : Nat) :
    (x :: acc).reverse.getD acc.length 0 = x := by
  simp [List.getD_eq_getElem?_getD]

theorem strRecN_congr (b : Array UInt8) (i w j w' pre vs ve : Word)
    (h : nextMemberN b i w = nextMemberN b j w') :
    strRecN b i w pre vs ve = strRecN b j w' pre vs ve := by
  conv => lhs; rw [strRecN]
  conv => rhs; rw [strRecN]
  simp only [h]

theorem numRecN_congr (b : Array UInt8) (i w j w' pre n : Word)
    (h : nextMemberN b i w = nextMemberN b j w') :
    numRecN b i w pre n = numRecN b j w' pre n := by
  conv => lhs; rw [numRecN]
  conv => rhs; rw [numRecN]
  simp only [h]

theorem recN_congr (b : Array UInt8) (i w j w' : Word) (f : Fld)
    (h : nextMemberN b i w = nextMemberN b j w') : recN b i w f = recN b j w' f := by
  conv => lhs; rw [recN]
  conv => rhs; rw [recN]
  simp only [h]

/-- What a name record's words say: the kind `k` (`1`: `str`, `2`: `num`), `pre`, and the
string's body or the number. -/
def NameR (b : ByteArray) : NameRec → Word → Word → Word → Word → Prop
  | .str p s, k, a, c, d => k = 1 ∧ ItemR a p ∧ (c ≠ 0 → StrR b c d s)
  | .num p n, k, a, c, _ => k = 2 ∧ ItemR a p ∧ ItemR c n

/-- What the line loop's words say about con-leche's payload so far. -/
def PlR (b : ByteArray) : LinePayload → Fld → Prop
  | .absent, _ => True
  | .name r, f => NameR b r f.pl f.a f.c f.d
  | .level (.succ u), f => f.pl = 3 ∧ ItemR f.a u
  | .level (.max u v), f => f.pl = 4 ∧ ItemR f.a u ∧ ItemR f.c v
  | .level (.imax u v), f => f.pl = 5 ∧ ItemR f.a u ∧ ItemR f.c v
  | .level (.param n), f => f.pl = 6 ∧ ItemR f.a n
  | .header, f => f.pl = 7
  | .expr _, _ => False
  | .decl _, _ => False

/-- What `rec_line_loop`'s words say about the line's record. -/
def RecR (b : ByteArray) : LineRec → Fld → Prop
  | .name i r, f => ItemR f.idx i ∧ PlR b (.name r) f
  | .level i r, f => ItemR f.idx i ∧ PlR b (.level r) f
  | .header, f => f.pl = 7
  | _, _ => False

section kit
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-! ## `read_nat` -/

omit h64 hsize in
theorem digit_sub (c : UInt8) : (c.toUInt64 - 48) &&& 255 = (c - 48).toUInt64 := by
  revert c; decide

theorem rdLoop_link (v e : USize) (x : UInt64) (he : e.toNat ≤ b.size) :
    rdLoopN b.data v.toUInt64 e.toUInt64 x = readNat64 b v e x := by
  fun_induction readNat64 b v e x with
  | case1 i acc h hie ih =>
    rw [rdLoopN_step _ _ _ _ ((lt_toUInt64_iff _ _).mp hie), ← succ_toUInt64 b h64 hsize,
      byteW_eq b h64 hsize, digit_sub]
    simp only [uget_byteAt _ i h] at ih ⊢
    exact ih
  | case2 i acc h hie => rw [rdLoopN_stop _ _ _ _ (fun h' => hie ((lt_toUInt64_iff _ _).mpr h'))]
  | case3 i acc h =>
    have := usizeGe b i h64 (by omega) h
    have hb : b.data.size = b.size := rfl
    rw [rdLoopN_stop _ _ _ _ (fun h' => by
      have := (lt_toUInt64_iff _ _).mpr h'; rw [USize.lt_iff_toNat_lt] at this; omega)]

theorem rdNat_link (v e : USize) (hve : v ≤ e) (he : e.toNat ≤ b.size) :
    ItemR (rdNatN b.data v.toUInt64 e.toUInt64) (readNatAt b v e) := by
  unfold rdNatN
  split
  · exact itemR_none _
  · rename_i hlong
    intro _
    have hv : v.toNat < 2 ^ 63 := by have := USize.le_iff_toNat_le.mp hve; omega
    have h18 : e - v ≤ 18 := by
      rw [USize.le_iff_toNat_le, USize.toNat_sub_of_le _ _ hve]
      have : ¬ v.toNat + 18 < e.toNat := by
        intro h'; apply hlong
        rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, USize.toNat_toUInt64, USize.toNat_toUInt64]
        simp; omega
      have : (18 : USize).toNat = 18 := by
        simp
      omega
    rw [readNatAt, ite_eq_left h18, rdLoop_link b h64 hsize v e 0 he]

/-! ## `rec_nat_list` -/

theorem pair_link (i : USize) (acc : List Nat) (w : Bool) (us : List Nat) (e : USize)
    (cnt x0 x1 : Word) (h : scanNatListLoop b i acc w = .ok us e)
    (hc : cnt.toNat = acc.length) (hl : acc.length ≤ i.toNat)
    (h0 : 0 < acc.length → ItemR x0 (acc.reverse.getD 0 0))
    (h1 : 1 < acc.length → ItemR x1 (acc.reverse.getD 1 0)) :
    (pairN b.data i.toUInt64 cnt x0 x1).1 = e.toUInt64 ∧
      (0 < us.length → ItemR (pairN b.data i.toUInt64 cnt x0 x1).2.1 (us.getD 0 0)) ∧
      (1 < us.length → ItemR (pairN b.data i.toUInt64 cnt x0 x1).2.2 (us.getD 1 0)) := by
  rw [scanNatListLoop] at h
  by_cases hi : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp hi
    have hcw := byteW_eq b h64 hsize i
    have hs := succ_toUInt64 b h64 hsize i
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    have hin := usizeInBounds b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      have hne : byteW b.data i.toUInt64 ≠ 93 := by
        rw [hcw]; intro h'; have := (u8_toUInt64_eq _ 93 (by decide)).mp h'
        rw [this] at hws; exact absurd hws (by decide)
      have hnd : ¬ (48 ≤ byteW b.data i.toUInt64 ∧ byteW b.data i.toUInt64 ≤ 57) := by
        rw [hcw, ← digit_iff]; intro h'; simp [isWs, isDigit] at hws h'; grind
      rw [pairN_other _ _ _ _ _ hlt hne hnd, ← hs]
      exact pair_link (i + 1) acc w us e cnt x0 x1 h hc (by omega) h0 h1
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h93 : byteAt b i = 93
    · simp only [h93, show ((93 : UInt8) == 93) = true from rfl, ite_true] at h
      split at h
      · simp at h
      · obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
        rw [pairN_close _ _ _ _ _ hlt (by rw [hcw, h93]; rfl), hs]
        refine ⟨rfl, fun hu => h0 (by simpa using hu), fun hu => h1 (by simpa using hu)⟩
    have h93' : byteW b.data i.toUInt64 ≠ 93 := by
      rw [hcw]; exact fun h' => h93 ((u8_toUInt64_eq _ 93 (by decide)).mp h')
    simp only [show (byteAt b i == 93) = false by simpa using h93, Bool.false_eq_true, ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h
      · simp at h
      have hnd : ¬ (48 ≤ byteW b.data i.toUInt64 ∧ byteW b.data i.toUInt64 ≤ 57) := by
        rw [hcw, h44]; decide
      rw [pairN_other _ _ _ _ _ hlt h93' hnd, ← hs]
      exact pair_link (i + 1) acc true us e cnt x0 x1 h hc (by omega) h0 h1
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true, ite_false] at h
    by_cases hd : isDigit (byteAt b i) = true
    · simp only [hd, ite_true] at h
      split at h
      · simp at h
      have hd' := (digit_iff _).mp hd
      rw [← hcw] at hd'
      split at h
      · simp at h
      rename_i hne
      split at h
      · rename_i hie
        have hne' := numEnd_toUInt64_eq b h64 (by omega) i
        have hieW : i.toUInt64 < UInt64.ofNat (L.Scan.Leaves.numEndN b.data i.toUInt64.toNat) := by
          rw [USize.toNat_toUInt64, ← hne']; exact (lt_toUInt64_iff _ _).mp hie
        rw [pairN_digit _ _ _ _ _ hlt h93' hd' hieW]
        rw [USize.toNat_toUInt64, ← hne']
        have hie' := USize.lt_iff_toNat_lt.mp hie
        have hle : (numEnd b i).toNat ≤ b.size := by
          have := numEnd_toNat_eq b h64 (by omega) i
          rw [this]; exact L.Scan.Values.numEndN_le b.data i.toNat (by have := usizeInBounds b i hi; have hb : b.data.size = b.size := rfl; omega)
        have hR := rdNat_link b h64 hsize i (numEnd b i) (USize.le_of_lt hie) hle
        have hcnt : (cnt + 1).toNat = (readNatAt b i (numEnd b i) :: acc).length := by
          rw [UInt64.toNat_add, hc]; simp; have := usizeInBounds b i hi; omega
        refine pair_link (numEnd b i) _ false us e (cnt + 1) _ _ h hcnt
          (by simp only [List.length_cons]; omega) ?_ ?_
        · intro _
          by_cases hc0 : acc.length = 0
          · have : cnt = 0 := UInt64.toNat_inj.mp (by rw [hc, hc0]; rfl)
            rw [ite_eq_left this]
            have : acc = [] := List.length_eq_zero_iff.mp hc0
            subst this; simpa using hR
          · have : cnt ≠ 0 := fun h' => hc0 (by rw [← hc, h']; rfl)
            rw [ite_eq_right this, getD_rev_cons acc _ 0 (by omega)]
            exact h0 (by omega)
        · intro hlen
          by_cases hc1 : acc.length = 1
          · have : cnt = 1 := UInt64.toNat_inj.mp (by rw [hc, hc1]; rfl)
            rw [ite_eq_left this, ← hc1, getD_rev_cons_self]
            exact hR
          · have : cnt ≠ 1 := fun h' => hc1 (by rw [← hc, h']; rfl)
            rw [ite_eq_right this, getD_rev_cons acc _ 1 (by simp at hlen; omega)]
            exact h1 (by simp at hlen; omega)
      · simp at h
    · simp only [hd, Bool.false_eq_true, ite_false] at h
      simp at h
  · rw [dite_eq_right hi] at h; simp at h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b i›; omega)

theorem pairEntry_link (v : USize) (x y : Nat) (e : USize) (h : scanNatList b v = .ok [x, y] e) :
    (pairEntryN b.data v.toUInt64).1 = e.toUInt64 ∧ ItemR (pairEntryN b.data v.toUInt64).2.1 x ∧
      ItemR (pairEntryN b.data v.toUInt64).2.2 y := by
  unfold scanNatList at h
  split at h
  · rename_i hc
    have hi : v < b.usize := by
      refine Classical.byContradiction fun hn => ?_
      have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
      rw [h0] at hc; exact absurd hc (by decide)
    have hv1 : (v + 1).toNat = v.toNat + 1 := usizeStep b v hi
    have := pair_link b h64 hsize (v + 1) [] true [x, y] e 0 0 0 h rfl (by simp)
      (by simp) (by simp)
    unfold pairEntryN
    rw [← succ_toUInt64 b h64 hsize]
    exact ⟨this.1, this.2.1 (by simp), this.2.2 (by simp)⟩
  · cases h

/-! ## A string's body -/

theorem hasEscape_noEsc (j e : USize) : hasEscape b j e = true → ¬ NoEsc b j.toNat e.toNat := by
  fun_induction hasEscape b j e with
  | case1 j h hlt hc =>
    intro _ hn
    apply hn j.toNat (Nat.le_refl _) (USize.lt_iff_toNat_lt.mp hlt)
    have hc' : b.uget j (usizeInBounds b j h) = 92 := by simpa using hc
    have hin := usizeInBounds b j h
    simp only [ByteArray.uget, Array.getD] at hc' ⊢
    rw [dite_eq_left (by exact hin)]; exact hc'
  | case2 j h hlt hc ih =>
    intro he hn
    have := usizeStep b j h
    exact ih he (fun k hk1 hk2 => hn k (by omega) hk2)
  | case3 => simp
  | case4 => simp

theorem scanString_strOK (v : USize) (x : String) (e' : USize)
    (h : ConLeche.Frontend.scanString b v = .ok x e') :
    StrOK b (v.toUInt64 + 1) (e'.toUInt64 - 1) x := by
  unfold ConLeche.Frontend.scanString at h
  split at h; cases h; rename_i hq
  have hv : v < b.usize := by
    refine Classical.byContradiction fun hn => ?_
    have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
    rw [h0] at hq; exact hq (by decide)
  have hv1 : (v.toUInt64 + 1).toNat = (v + 1).toNat := by
    rw [← succ_toUInt64 b h64 hsize, USize.toNat_toUInt64]
  have hc := strClose_toNat_eq b h64 (by omega) (v + 1)
  dsimp only at h
  split at h; cases h; rename_i hz
  have hz' : strClose b (v + 1) ≠ 0 := by simpa using hz
  have hcn : L.Examples.strCloseN b.data (v + 1).toNat ≠ 0 := by
    rw [← hc]; intro h0; exact hz' (USize.toNat_inj.mp (by rw [h0]; rfl))
  have hlt := (L.Examples.strCloseN_bounds b.data (v + 1).toNat hcn).2
  have hbs : b.data.size = b.size := rfl
  have he1 : ((strClose b (v + 1) + 1).toUInt64 - 1).toNat = (strClose b (v + 1)).toNat := by
    rw [succ_toUInt64 b h64 hsize, UInt64.add_sub_cancel, USize.toNat_toUInt64]
  split at h
  · rename_i hesc
    split at h
    · obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
      intro hn
      rw [hv1, he1] at hn
      exact absurd hn (hasEscape_noEsc b h64 hsize _ _ hesc)
    · cases h
  · split at h
    · rename_i s hs
      obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
      intro _
      rw [hv1, he1]; exact hs
    · cases h

/-! ## `next_member` on con-leche's bytes -/

theorem nm_ws (i : USize) (x : Word) (hi : i < b.usize) (hws : isWs (byteAt b i) = true) :
    nextMemberN b.data i.toUInt64 x = nextMemberN b.data (i + 1).toUInt64 x := by
  rw [succ_toUInt64 b h64 hsize]
  exact nextMemberN_ws _ _ _ ((lt_usize_iff b h64 hsize i).mp hi)
    (by rw [byteW_eq b h64 hsize]; exact (ws_iff _).mp hws)

theorem nm_notws (i : USize) (hws : ¬ isWs (byteAt b i) = true) :
    ¬ (byteW b.data i.toUInt64 = 32 ∨ byteW b.data i.toUInt64 = 9 ∨ byteW b.data i.toUInt64 = 13) := by
  rw [byteW_eq b h64 hsize, ← ws_iff]; exact hws

theorem nm_close (i : USize) (x : Word) (hi : i < b.usize) (hws : ¬ isWs (byteAt b i) = true)
    (hc : byteAt b i = 125) : nextMemberN b.data i.toUInt64 x = ⟨1, i.toUInt64, x, 0, 0⟩ :=
  nextMemberN_close _ _ _ ((lt_usize_iff b h64 hsize i).mp hi) (nm_notws b h64 hsize i hws)
    (by rw [byteW_eq b h64 hsize, hc]; rfl)

theorem nm_comma (i : USize) (hi : i < b.usize) (hws : ¬ isWs (byteAt b i) = true)
    (hc : byteAt b i = 44) : nextMemberN b.data i.toUInt64 0 = nextMemberN b.data (i + 1).toUInt64 1 := by
  rw [nextMemberN_comma _ _ _ ((lt_usize_iff b h64 hsize i).mp hi) (nm_notws b h64 hsize i hws)
    (by rw [byteW_eq b h64 hsize, hc]; decide) (by rw [byteW_eq b h64 hsize, hc]; rfl),
    ite_eq_right (by decide), succ_toUInt64 b h64 hsize]

theorem nm_key (i : USize) (hi : i < b.usize) (hc : byteAt b i = 34) (hk : keyEnd b (i + 1) ≠ 0)
    (hv : valueAt b i (keyEnd b (i + 1)) ≠ i) :
    nextMemberN b.data i.toUInt64 1 = ⟨2, i.toUInt64, 1,
      UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx,
      (valueAt b i (keyEnd b (i + 1))).toUInt64⟩ := by
  have hq := nextMemberN_quote_link b h64 hsize i 1 hi hc
  simp only [show (1 : Word) ≠ 0 by decide, ite_false, hk, hv] at hq
  exact hq

/-- The value of a numeric slot is inside the buffer. -/
theorem numEnd_le (v : USize) (hv : v.toNat ≤ b.size) : (numEnd b v).toNat ≤ b.size := by
  rw [numEnd_toNat_eq b h64 (by omega)]
  exact L.Scan.Values.numEndN_le b.data v.toNat hv

/-- A key's value position is inside the buffer. -/
theorem nm_key_le (i : USize) (hi : i < b.usize) (hc : byteAt b i = 34) (hk : keyEnd b (i + 1) ≠ 0)
    (hv : valueAt b i (keyEnd b (i + 1)) ≠ i) : (valueAt b i (keyEnd b (i + 1))).toNat ≤ b.size := by
  have hm := nm_key b h64 hsize i hi hc hk hv
  have := L.Scan.Member.nextMemberN_val_le b.data i.toUInt64 1
    (by have : b.data.size = b.size := rfl; omega) (by rw [hm])
  rw [hm] at this; simpa using this

theorem le_numEnd (v : USize) (_hvle : v.toNat ≤ b.size) : v ≤ numEnd b v := by
  have := numEnd_toNat_eq b h64 (by omega) v
  rw [USize.le_iff_toNat_le, this]; exact L.Scan.Values.numEndN_ge _ _

/-- A number value: `slot_nat`'s end and `read_nat`'s word. -/
theorem num_val (i v : USize) (hne : ¬ numEnd b v = v) (hie : i < numEnd b v)
    (hvle : v.toNat ≤ b.size) :
    L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64 = (numEnd b v).toUInt64 ∧
    ItemR (rdNatN b.data v.toUInt64 (numEnd b v).toUInt64) (readNatAt b v (numEnd b v)) :=
  ⟨by rw [slotNatN_link b h64 hsize, ite_eq_right hne, ite_eq_left hie],
    rdNat_link b h64 hsize v (numEnd b v) (le_numEnd b h64 hsize v hvle) (numEnd_le b h64 hsize v hvle)⟩

/-! ## `rec_str_name`, `rec_num_name` -/

theorem strRec_link (i : USize) (w : Bool) (seen : UInt32) (pre : Nat) (s : String) (r : NameRec)
    (e : USize) (pw vs ve : Word) (h : scanStrNameLoop b i w seen pre s = .ok r e)
    (hp : ItemR pw pre) (hs : vs ≠ 0 → StrR b vs ve s) :
    (strRecN b.data i.toUInt64 (bw w) pw vs ve).1 = e.toUInt64 ∧
      NameR b r 1 (strRecN b.data i.toUInt64 (bw w) pw vs ve).2.1
        (strRecN b.data i.toUInt64 (bw w) pw vs ve).2.2.1
        (strRecN b.data i.toUInt64 (bw w) pw vs ve).2.2.2 := by
  rw [scanStrNameLoop] at h
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      rw [strRecN_congr _ _ _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact strRec_link (i + 1) w seen pre s r e pw vs ve h hp hs
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h125 : byteAt b i = 125
    · simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true] at h
      split at h; cases h
      split at h; cases h
      obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
      rw [strRecN_close _ _ _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125]),
        nm_close b h64 hsize i _ hi hws h125, succ_toUInt64 b h64 hsize]
      exact ⟨rfl, rfl, hp, hs⟩
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true,
      ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = false := by simpa using hw
      subst hw'
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [strRecN_congr _ _ _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact strRec_link (i + 1) true seen pre s r e pw vs ve h hp hs
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true,
      ite_false] at h
    by_cases h34 : byteAt b i = 34
    · simp only [h34, show ((34 : UInt8) == 34) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = true := by simpa using hw
      subst hw'
      split at h; cases h; rename_i hk
      split at h; cases h; rename_i hv
      have hk' : keyEnd b (i + 1) ≠ 0 := by simpa using hk
      have hv' : valueAt b i (keyEnd b (i + 1)) ≠ i := by simpa using hv
      have hm := nm_key b h64 hsize i hi h34 hk' hv'
      simp only [bw, ite_true]
      rw [strRecN_key _ _ _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      have hvle := nm_key_le b h64 hsize i hi h34 hk' hv'
      simp only [hm]
      generalize valueAt b i (keyEnd b (i + 1)) = v at h hvle
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at h
      split at h
      · -- `pre`
        simp only [show UInt64.ofNat Key.kPre.ctorIdx = 47 from rfl, ite_true]
        split at h; cases h
        split at h; cases h; rename_i hne
        split at h
        · rename_i hie
          obtain ⟨hsl, hR⟩ := num_val b h64 hsize i v (by simpa using hne) hie hvle
          rw [hsl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact strRec_link (numEnd b v) false _ _ s r e _ vs ve h hR hs
        · cases h
      · -- `str`
        simp only [show UInt64.ofNat Key.kStr.ctorIdx = 56 from rfl,
          show (56 : Word) ≠ 47 by decide, ite_false]
        split at h; cases h
        split at h; cases h; rename_i x e' hx
        split at h
        · rename_i hie
          have hse : L.Scan.Str.scanStringN b.data v.toUInt64 = e'.toUInt64 := by
            rw [← ConAgua.Scan.StrLink.scanString_eq h64 b hsize v, hx]; rfl
          rw [hse, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact strRec_link e' false _ pre x r e _ _ _ h hp (fun _ => ⟨v, e', rfl, rfl, hx⟩)
        · cases h
      · cases h
    · simp only [show (byteAt b i == 34) = false by simpa using h34, Bool.false_eq_true,
        ite_false] at h
      cases h
  · rw [dite_eq_right hi] at h; cases h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b _›; omega)
    | (have := USize.lt_iff_toNat_lt.mp ‹i < _›; omega)

theorem numRec_link (i : USize) (w : Bool) (seen : UInt32) (n pre : Nat) (r : NameRec)
    (e : USize) (pw nw : Word) (h : scanNumNameLoop b i w seen n pre = .ok r e)
    (hp : ItemR pw pre) (hn : ItemR nw n) :
    (numRecN b.data i.toUInt64 (bw w) pw nw).1 = e.toUInt64 ∧
      NameR b r 2 (numRecN b.data i.toUInt64 (bw w) pw nw).2.1
        (numRecN b.data i.toUInt64 (bw w) pw nw).2.2 0 := by
  rw [scanNumNameLoop] at h
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      rw [numRecN_congr _ _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact numRec_link (i + 1) w seen n pre r e pw nw h hp hn
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h125 : byteAt b i = 125
    · simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true] at h
      split at h; cases h
      split at h; cases h
      obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
      rw [numRecN_close _ _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125]),
        nm_close b h64 hsize i _ hi hws h125, succ_toUInt64 b h64 hsize]
      exact ⟨rfl, rfl, hp, hn⟩
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true,
      ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = false := by simpa using hw
      subst hw'
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [numRecN_congr _ _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact numRec_link (i + 1) true seen n pre r e pw nw h hp hn
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true,
      ite_false] at h
    by_cases h34 : byteAt b i = 34
    · simp only [h34, show ((34 : UInt8) == 34) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = true := by simpa using hw
      subst hw'
      split at h; cases h; rename_i hk
      split at h; cases h; rename_i hv
      have hk' : keyEnd b (i + 1) ≠ 0 := by simpa using hk
      have hv' : valueAt b i (keyEnd b (i + 1)) ≠ i := by simpa using hv
      have hm := nm_key b h64 hsize i hi h34 hk' hv'
      simp only [bw, ite_true]
      rw [numRecN_key _ _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      have hvle := nm_key_le b h64 hsize i hi h34 hk' hv'
      simp only [hm]
      generalize valueAt b i (keyEnd b (i + 1)) = v at h hvle
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at h
      split at h
      · -- `i`
        simp only [show UInt64.ofNat Key.kI.ctorIdx = 16 from rfl]
        split at h; cases h
        split at h; cases h; rename_i hne
        split at h
        · rename_i hie
          obtain ⟨hsl, hR⟩ := num_val b h64 hsize i v (by simpa using hne) hie hvle
          rw [hsl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie),
            ite_eq_right (show (16 : Word) ≠ 47 by decide)]
          exact numRec_link (numEnd b v) false _ _ pre r e pw _ h hp hR
        · cases h
      · -- `pre`
        simp only [show UInt64.ofNat Key.kPre.ctorIdx = 47 from rfl]
        split at h; cases h
        split at h; cases h; rename_i hne
        split at h
        · rename_i hie
          obtain ⟨hsl, hR⟩ := num_val b h64 hsize i v (by simpa using hne) hie hvle
          rw [hsl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie), ite_eq_left True.intro]
          exact numRec_link (numEnd b v) false _ n _ r e _ nw h hR hn
        · cases h
      · cases h
    · simp only [show (byteAt b i == 34) = false by simpa using h34, Bool.false_eq_true,
        ite_false] at h
      cases h
  · rw [dite_eq_right hi] at h; cases h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b _›; omega)
    | (have := USize.lt_iff_toNat_lt.mp ‹i < _›; omega)

theorem obj_open (v : USize) (hc : (byteAt b v == 123) = true) :
    v < b.usize ∧ (v + 1).toUInt64 = v.toUInt64 + 1 := by
  have hv : v < b.usize := by
    refine Classical.byContradiction fun hn => ?_
    have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
    rw [h0] at hc; exact absurd hc (by decide)
  exact ⟨hv, succ_toUInt64 b h64 hsize v⟩

theorem strEntry_link (v : USize) (r : NameRec) (e : USize) (h : scanStrName b v = .ok r e) :
    (strRecEntryN b.data v.toUInt64).1 = e.toUInt64 ∧
      NameR b r 1 (strRecEntryN b.data v.toUInt64).2.1 (strRecEntryN b.data v.toUInt64).2.2.1
        (strRecEntryN b.data v.toUInt64).2.2.2 := by
  unfold scanStrName at h
  split at h
  · rename_i hc
    unfold strRecEntryN
    rw [← (obj_open b h64 hsize v hc).2]
    exact strRec_link b h64 hsize (v + 1) true 0 0 "" r e 0 0 0 h itemR_zero (fun h => absurd rfl h)
  · cases h

theorem numEntry_link (v : USize) (r : NameRec) (e : USize) (h : scanNumName b v = .ok r e) :
    (numRecEntryN b.data v.toUInt64).1 = e.toUInt64 ∧
      NameR b r 2 (numRecEntryN b.data v.toUInt64).2.1 (numRecEntryN b.data v.toUInt64).2.2 0 := by
  unfold scanNumName at h
  split at h
  · rename_i hc
    unfold numRecEntryN
    rw [← (obj_open b h64 hsize v hc).2]
    exact numRec_link b h64 hsize (v + 1) true 0 0 0 r e 0 0 h itemR_zero itemR_zero
  · cases h

/-! ## `rec_line_loop` -/

omit h64 hsize in
theorem plR_idx (pl : LinePayload) (f : Fld) (x : Word) (h : PlR b pl f) :
    PlR b pl ⟨f.pl, x, f.a, f.c, f.d⟩ := by
  rcases pl with _ | (_ | _) | (_ | _ | _ | _) | _ | _ | _ <;> exact h

omit h64 hsize in
theorem nameR_d (r : NameRec) (a c d d' : Word) (h : NameR b r 2 a c d) :
    NameR b r 2 a c d' := by
  cases r
  · exact absurd h.1 (by decide)
  · exact h

theorem recLine_link (i : USize) (w : Bool) (ik : UInt8) (idx : Nat) (pl : LinePayload) (f : Fld)
    (r : LineRec) (e : USize) (h : scanLineLoop b i w ik idx pl = .ok r e)
    (hI : ItemR f.idx idx) (hP : PlR b pl f) :
    (recN b.data i.toUInt64 (bw w) f).pl ≠ 0 → RecR b r (recN b.data i.toUInt64 (bw w) f) := by
  rw [scanLineLoop.eq_def] at h
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      rw [recN_congr _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact recLine_link (i + 1) w ik idx pl f r e h hI hP
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h125 : byteAt b i = 125
    · simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true] at h
      rw [recN_close _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125])]
      split at h; cases h
      cases pl
      · simp at h
      · by_cases hk : ik = 1
        · subst hk; obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
          exact fun _ => ⟨hI, hP⟩
        · simp [hk] at h
      · by_cases hk : ik = 2
        · subst hk; obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
          exact fun _ => ⟨hI, hP⟩
        · simp [hk] at h
      · exact hP.elim
      · exact hP.elim
      · by_cases hk : ik = 0
        · subst hk; obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
          exact fun _ => hP
        · simp [hk] at h
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true,
      ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = false := by simpa using hw
      subst hw'
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [recN_congr _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact recLine_link (i + 1) true ik idx pl f r e h hI hP
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true,
      ite_false] at h
    by_cases h34 : byteAt b i = 34
    · simp only [h34, show ((34 : UInt8) == 34) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = true := by simpa using hw
      subst hw'
      split at h; cases h; rename_i hk
      split at h; cases h; rename_i hv
      have hk' : keyEnd b (i + 1) ≠ 0 := by simpa using hk
      have hv' : valueAt b i (keyEnd b (i + 1)) ≠ i := by simpa using hv
      have hm := nm_key b h64 hsize i hi h34 hk' hv'
      simp only [bw, ite_true]
      rw [recN_key _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      have hvle := nm_key_le b h64 hsize i hi h34 hk' hv'
      simp only [hm]
      generalize valueAt b i (keyEnd b (i + 1)) = v at h hvle
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at h
      cases K
      all_goals (try dsimp only at h)
      all_goals (try (cases h; done))
      all_goals simp (config := {decide := true}) only [↓reduceIte]
      all_goals (try exact False.elim)
      case kIn | kIl | kIe | kSucc | kParam =>
        split at h; cases h
        split at h; cases h; rename_i hne
        split at h
        · rename_i hie
          obtain ⟨hsl, hR⟩ := num_val b h64 hsize i v (by simpa using hne) hie hvle
          rw [hsl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          first
            | exact recLine_link (numEnd b v) false _ _ _ _ r e h hR (plR_idx b _ _ _ hP)
            | exact recLine_link (numEnd b v) false _ _ _ _ r e h hI ⟨rfl, hR⟩
        · cases h
      case kMax | kImax =>
        split at h; cases h
        split at h; cases h; rename_i us e' hus
        split at h
        · rename_i x y
          split at h
          · rename_i hie
            have hp := pairEntry_link b h64 hsize v x y e' hus
            rw [hp.1, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
            exact recLine_link e' false _ _ _ _ r e h hI ⟨rfl, hp.2.1, hp.2.2⟩
          · cases h
        · cases h
      case kStr =>
        split at h; cases h
        split at h; cases h; rename_i r' e' hr
        split at h
        · rename_i hie
          have hp := strEntry_link b h64 hsize v r' e' hr
          rw [hp.1, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact recLine_link e' false _ _ _ _ r e h hI hp.2
        · cases h
      case kNum =>
        split at h; cases h
        split at h; cases h; rename_i r' e' hr
        split at h
        · rename_i hie
          have hp := numEntry_link b h64 hsize v r' e' hr
          rw [hp.1, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact recLine_link e' false _ _ _ _ r e h hI (nameR_d b r' _ _ _ _ hp.2)
        · cases h
      case kMeta =>
        split at h; cases h
        split at h; cases h; rename_i hc
        split at h; cases h
        split at h
        · rename_i hie
          have hmeta : metaN b.data v.toUInt64 = (skipBraced b (v + 1) 0).toUInt64 := by
            unfold metaN
            rw [ConAgua.Scan.LineLink.skip_link b h64 hsize v, ite_eq_left (by simpa using hc)]
          rw [hmeta, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact recLine_link _ false _ _ _ _ r e h hI rfl
        · cases h
    · simp only [show (byteAt b i == 34) = false by simpa using h34, Bool.false_eq_true,
        ite_false] at h
      cases h
  · rw [dite_eq_right hi] at h; cases h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹i < numEnd b _›; omega)
    | (have := USize.lt_iff_toNat_lt.mp ‹i < _›; omega)

end kit

end ConAgua.Front.FieldsLink
