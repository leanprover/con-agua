module

public import ConAgua.Scan.KeyLink
public import ConAgua.Scan.ValuesLink
public import ConAgua.Scan.StrLink
public import ConAgua.Scan.LitLink
public import ConAgua.Scan.Records
import ConAgua.Census.Attr

@[expose] public section


/-!
# The record loops, linked to con-leche

Each of con-leche's 18 record loops (`scan*Loop`, `ConLeche/Frontend/Scan/Fast.lean`) against the
generic model `objN` with its record's `bit`/`val`/`mask` (`ConAgua.Scan.Records`), the 4 lists
of records against `objListN`, and each entry (`scan*`) against its model (`appN`, `rulesN`, …),
in ok-ness and position (`okW`).

One generic theorem does the work for every loop: `objN_link` from `ObjLoop`, the shape every
con-leche record loop has (its six byte arms and, at a key, `KeyStep`: the key's bit, the
duplicate check, the value scanned and the step to the next member). A loop's `ObjLoop` is proved
by one tactic, `obj_loop`, the same for all 18: it unfolds the loop once and, at a key, does
cases on the key (`Key`, 66 constructors) and closes every arm with `keyStep_unknown`, or
`keyStep_guard` and the value's kind (`key_value`: a `numEnd` slot, `scanBinderInfo`'s
end-or-zero, or a `ScanRes` scanner, whose link `link_val` finds). The lists likewise
(`objListN_link`, `ListLoop`, `list_loop`). The record state con-leche carries (the fields it
reads) is a tuple `st` the model ignores.
-/

namespace ConAgua.Scan.RecordsLink
open ConLeche.Frontend ConAgua.Scan
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Records
open L.Scan.Leaves (keyEndN)
open L.Scan.Key (keyAtN valueAtN)

/-! ## The kit -/

/-- A `Bool` flag as the model's word. -/
def bw (w : Bool) : Word := if w then 1 else 0

theorem bw_ne_zero (w : Bool) : bw w ≠ 0 ↔ w = true := by cases w <;> simp [bw]

theorem u8_toUInt64_eq (a : UInt8) (n : Nat) (hn : n < 256) :
    a.toUInt64 = (OfNat.ofNat n : Word) ↔ a = (OfNat.ofNat n : UInt8) := by
  rw [← UInt8_ofNat_toUInt64 n hn, UInt8.toUInt64_inj]

theorem u32_toUInt64_eq_zero (a : UInt32) : a.toUInt64 = 0 ↔ a = 0 :=
  (UInt32.toUInt64_inj (b := 0))

theorem keyEndN_bounds (b : Array UInt8) (j : Nat) (h : keyEndN b j ≠ 0) :
    j ≤ keyEndN b j ∧ keyEndN b j < b.size := by
  fun_induction keyEndN b j with
  | case1 j h1 _ => omega
  | case2 => simp at h
  | case3 j _ _ _ ih => have := ih h; omega
  | case4 => simp at h

section kit
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lt_usize_iff (i : USize) : i < b.usize ↔ i.toUInt64 < UInt64.ofNat b.data.size := by
  rw [lt_toUInt64_iff, usize_toUInt64_eq b h64 (by omega)]; rfl

theorem byteW_eq (i : USize) : byteW b.data i.toUInt64 = (byteAt b i).toUInt64 :=
  (byteAt_toUInt64_eq b i h64 (by omega)).symm

theorem succ_toUInt64 (i : USize) : (i + 1).toUInt64 = i.toUInt64 + 1 := by
  rw [add_toUInt64 h64, ofNat_toUInt64 h64 1]

end kit

theorem ws_iff (c : UInt8) : isWs c = true ↔ (c.toUInt64 = 32 ∨ c.toUInt64 = 9 ∨ c.toUInt64 = 13) := by
  rw [u8_toUInt64_eq c 32 (by decide), u8_toUInt64_eq c 9 (by decide),
    u8_toUInt64_eq c 13 (by decide)]
  simp only [isWs, Bool.or_eq_true, beq_iff_eq, or_assoc]

theorem uget_byteAt (b : ByteArray) (i : USize) (h : i < b.usize) (hh) :
    b.uget i hh = byteAt b i := by
  unfold byteAt; rw [dite_eq_left h]

/-! ## The generic object loop -/

/-- `objN` is a function of what `nextMemberN` returns. -/
theorem objN_congr (bit : Word → Word) (val : Word → Word → Word → Word) (mask : Word)
    (b : Array UInt8) (i w j w' seen : Word) (h : nextMemberN b i w = nextMemberN b j w') :
    objN bit val mask b i w seen = objN bit val mask b j w' seen := by
  conv => lhs; rw [objN]
  conv => rhs; rw [objN]
  simp only [h]

variable {σ α : Type}

/-- What a record loop does at a key `kc` whose value starts at `v`, against `objN`. -/
def KeyStep (F : USize → Bool → UInt32 → σ → ScanRes α) (bit : Word → Word)
    (val : Word → Word → Word → Word) (i v : USize) (seen : UInt32) (kc : Word)
    (r : ScanRes α) : Prop :=
  (okW r = 0 ∧ (bit kc = 0 ∨ seen.toUInt64 &&& bit kc ≠ 0 ∨
      ¬ i.toUInt64 < val kc i.toUInt64 v.toUInt64)) ∨
  (bit kc ≠ 0 ∧ seen.toUInt64 &&& bit kc = 0 ∧ ∃ e seen', e.toUInt64 = val kc i.toUInt64 v.toUInt64 ∧
    i.toUInt64 < e.toUInt64 ∧ seen'.toUInt64 = seen.toUInt64 ||| bit kc ∧
    ∃ st', okW r = okW (F e false seen' st'))

/-- The shape of a con-leche record loop `F` (its state, the record's fields, in `σ`). -/
structure ObjLoop (b : ByteArray) (F : USize → Bool → UInt32 → σ → ScanRes α) (mask : UInt32)
    (bit : Word → Word) (val : Word → Word → Word → Word) : Prop where
  stop : ∀ i w seen st, ¬ i < b.usize → okW (F i w seen st) = 0
  ws : ∀ i w seen st, i < b.usize → isWs (byteAt b i) = true → F i w seen st = F (i + 1) w seen st
  close : ∀ i w seen st, i < b.usize → byteAt b i = 125 →
    okW (F i w seen st) =
      if w = true ∧ seen ≠ 0 then 0 else if seen &&& mask ≠ mask then 0 else (i + 1).toUInt64
  comma : ∀ i w seen st, i < b.usize → byteAt b i = 44 →
    okW (F i w seen st) = if w = true then 0 else okW (F (i + 1) true seen st)
  quote : ∀ i w seen st, i < b.usize → byteAt b i = 34 →
    (w = false ∨ keyEnd b (i + 1) = 0 ∨ valueAt b i (keyEnd b (i + 1)) = i) →
    okW (F i w seen st) = 0
  key : ∀ i seen, i < b.usize → byteAt b i = 34 → keyEnd b (i + 1) ≠ 0 →
    valueAt b i (keyEnd b (i + 1)) ≠ i → ∀ st,
    KeyStep F bit val i (valueAt b i (keyEnd b (i + 1))) seen
      (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx) (F i true seen st)
  other : ∀ i w seen st, i < b.usize → isWs (byteAt b i) = false → byteAt b i ≠ 125 →
    byteAt b i ≠ 44 → byteAt b i ≠ 34 → okW (F i w seen st) = 0

section generic
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- The key `next_member` reads, through con-leche's `keyEnd`/`valueAt`/`keyAt`. -/
theorem nextMemberN_quote_link (i : USize) (w : Word) (h : i < b.usize) (hc : byteAt b i = 34) :
    nextMemberN b.data i.toUInt64 w =
      if w = 0 then .err
      else if keyEnd b (i + 1) = 0 then .err
      else if valueAt b i (keyEnd b (i + 1)) = i then .err
      else ⟨2, i.toUInt64, w, UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx,
        (valueAt b i (keyEnd b (i + 1))).toUInt64⟩ := by
  have hlt := (lt_usize_iff b h64 hsize i).mp h
  have hcw : byteW b.data i.toUInt64 = 34 := by
    rw [byteW_eq b h64 hsize, hc]; rfl
  rw [nextMemberN_quote b.data i.toUInt64 w hlt (by rw [hcw]; decide) (by rw [hcw]; decide)
    (by rw [hcw]; decide) hcw]
  have hs := succ_toUInt64 b h64 hsize i
  have hke : UInt64.ofNat (keyEndN b.data (i.toUInt64 + 1).toNat) = (keyEnd b (i + 1)).toUInt64 := by
    rw [← hs, USize.toNat_toUInt64, keyEnd_toUInt64_eq b h64 (by omega)]
  simp only [hke]
  by_cases hw : w = 0
  · simp [hw]
  simp only [hw, ite_false]
  by_cases hk : keyEnd b (i + 1) = 0
  · simp [hk]
  have hk' : (keyEnd b (i + 1)).toUInt64 ≠ 0 := by
    intro h0; apply hk; exact (eq_toUInt64_iff _ _).mpr (by rw [h0]; rfl)
  simp only [hk', hk, ite_false]
  have hv : valueAtN b.data i.toUInt64 (keyEnd b (i + 1)).toUInt64 =
      (valueAt b i (keyEnd b (i + 1))).toUInt64 := (valueAt_eq_valueAtN b h64 hsize _ _).symm
  rw [hv]
  have hv' : (valueAt b i (keyEnd b (i + 1))).toUInt64 = i.toUInt64 ↔
      valueAt b i (keyEnd b (i + 1)) = i := (eq_toUInt64_iff _ _).symm
  by_cases hvi : valueAt b i (keyEnd b (i + 1)) = i
  · simp [hvi]
  simp only [(not_congr hv').mpr hvi, hvi, ite_false]
  -- the key code
  have hkn := keyEnd_toNat_eq b h64 (by omega) (i + 1)
  have hkn0 : keyEndN b.data (i + 1).toNat ≠ 0 := by
    intro h0; apply hk; apply USize.toNat_inj.mp; rw [hkn, h0]; rfl
  have hb := keyEndN_bounds b.data _ hkn0
  have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i h
  have hsub : (keyEnd b (i + 1) - (i + 1)).toNat = (keyEnd b (i + 1)).toNat - (i.toNat + 1) := by
    rw [USize.toNat_sub_of_le _ _ (by rw [USize.le_iff_toNat_le]; omega), hi1]
  have hbs : b.data.size = b.size := rfl
  rw [keyAt_eq_keyAtN b h64 hsize i _ (by omega), sub_toUInt64 h64, hs]

theorem objN_link (F : USize → Bool → UInt32 → σ → ScanRes α) (mask : UInt32) (bit : Word → Word)
    (val : Word → Word → Word → Word) (H : ObjLoop b F mask bit val) (i : USize) (w : Bool)
    (seen : UInt32) (st : σ) :
    okW (F i w seen st) = objN bit val mask.toUInt64 b.data i.toUInt64 (bw w) seen.toUInt64 := by
  by_cases h : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp h
    have hcw := byteW_eq b h64 hsize i
    have hs := succ_toUInt64 b h64 hsize i
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i h
    have hin := usizeInBounds b i h
    by_cases hws : isWs (byteAt b i) = true
    · rw [H.ws i w seen st h hws, objN_congr _ _ _ _ _ _ (i.toUInt64 + 1) (bw w),
        objN_link F mask bit val H (i + 1) w seen st, hs]
      exact nextMemberN_ws _ _ _ hlt (by rw [hcw]; exact (ws_iff _).mp hws)
    have hws' : ¬ (byteW b.data i.toUInt64 = 32 ∨ byteW b.data i.toUInt64 = 9 ∨
        byteW b.data i.toUInt64 = 13) := by rw [hcw, ← ws_iff]; exact hws
    by_cases h125 : byteAt b i = 125
    · have h125' : byteW b.data i.toUInt64 = 125 := by rw [hcw, h125]; rfl
      rw [H.close i w seen st h h125, objN_close _ _ _ _ _ _ _
        (by rw [nextMemberN_close _ _ _ hlt hws' h125'])]
      rw [nextMemberN_close _ _ _ hlt hws' h125', hs]
      simp only [bw_ne_zero, ne_eq, u32_toUInt64_eq_zero, ← UInt32.toUInt64_and, UInt32.toUInt64_inj]
    have h125' : byteW b.data i.toUInt64 ≠ 125 := by
      rw [hcw]; exact fun h' => h125 ((u8_toUInt64_eq _ 125 (by decide)).mp h')
    by_cases h44 : byteAt b i = 44
    · have h44' : byteW b.data i.toUInt64 = 44 := by rw [hcw, h44]; rfl
      rw [H.comma i w seen st h h44]
      by_cases hw : w = true
      · rw [ite_eq_left hw, objN_err]
        rw [nextMemberN_comma _ _ _ hlt hws' h125' h44', ite_eq_left ((bw_ne_zero w).mpr hw)]; rfl
      · rw [ite_eq_right hw, objN_congr _ _ _ _ _ _ (i.toUInt64 + 1) 1,
          objN_link F mask bit val H (i + 1) true seen st, hs]
        · rfl
        rw [nextMemberN_comma _ _ _ hlt hws' h125' h44', ite_eq_right (by rw [bw_ne_zero]; exact hw)]
    have h44' : byteW b.data i.toUInt64 ≠ 44 := by
      rw [hcw]; exact fun h' => h44 ((u8_toUInt64_eq _ 44 (by decide)).mp h')
    by_cases h34 : byteAt b i = 34
    · have h34' : byteW b.data i.toUInt64 = 34 := by rw [hcw, h34]; rfl
      have hq := nextMemberN_quote_link b h64 hsize i (bw w) h h34
      by_cases hbad : w = false ∨ keyEnd b (i + 1) = 0 ∨ valueAt b i (keyEnd b (i + 1)) = i
      · rw [H.quote i w seen st h h34 hbad, objN_err]
        rw [hq]
        rcases hbad with hb | hb | hb
        · subst hb; rfl
        · simp [hb]; rfl
        · simp [hb]; rfl
      simp only [not_or] at hbad
      obtain ⟨hw, hk, hv⟩ := hbad
      have hw' : w = true := by simpa using hw
      subst hw'
      simp only [bw, ite_true, show (1 : Word) ≠ 0 by decide, ite_false, hk, hv] at hq
      have hk0 : (nextMemberN b.data i.toUInt64 1).tag ≠ 0 := by rw [hq]; exact (by decide : (2 : Word) ≠ 0)
      have hk1 : (nextMemberN b.data i.toUInt64 1).tag ≠ 1 := by rw [hq]; exact (by decide : (2 : Word) ≠ 1)
      have hkey := H.key i seen h h34 hk hv st
      simp only [bw, ite_true]
      rcases hkey with ⟨hr, hcase⟩ | ⟨hb, hd, e, seen', he, hie, hs', st', hr⟩
      · rw [hr]
        by_cases hb0 : bit (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx) = 0
        · rw [objN_unknown _ _ _ _ _ _ _ hk0 hk1 (by rw [hq]; exact hb0)]
        by_cases hd : seen.toUInt64 &&& bit (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx) ≠ 0
        · rw [objN_dup _ _ _ _ _ _ _ hk0 hk1 (by rw [hq]; exact hb0) (by rw [hq]; exact hd)]
        have hc : ¬ i.toUInt64 < val (UInt64.ofNat (keyAt b i (keyEnd b (i + 1) - (i + 1))).ctorIdx)
            i.toUInt64 (valueAt b i (keyEnd b (i + 1))).toUInt64 := by
          rcases hcase with hc | hc | hc
          · exact absurd hc hb0
          · exact absurd hc hd
          · exact hc
        rw [objN_noprog _ _ _ _ _ _ _ hk0 hk1 (by rw [hq]; exact hb0) (by rw [hq]; simpa using hd)
          (by rw [hq]; exact hc)]
      · rw [hr, objN_step _ _ _ _ _ _ _ e.toUInt64 seen'.toUInt64 hk0 hk1 (by rw [hq]; exact hb)
          (by rw [hq]; exact hd) (by rw [hq]; exact he.symm) (by rw [hq]; exact hie) (by rw [hq]; exact hs')]
        exact objN_link F mask bit val H e false seen' st'
    · have h34' : byteW b.data i.toUInt64 ≠ 34 := by
        rw [hcw]; exact fun h' => h34 ((u8_toUInt64_eq _ 34 (by decide)).mp h')
      rw [H.other i w seen st h (by simpa using hws) h125 h44 h34, objN_err]
      rw [nextMemberN_other _ _ _ hlt hws' h125' h44' h34']; rfl
  · rw [H.stop i w seen st h, objN_err]
    rw [nextMemberN_end]
    · rfl
    rw [← lt_usize_iff b h64 hsize]; exact h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (rw [UInt64.lt_iff_toNat_lt, USize.toNat_toUInt64, USize.toNat_toUInt64] at hie; omega)

end generic

/-! ## One key of a record loop -/

section keystep
variable {F : USize → Bool → UInt32 → σ → ScanRes α} {bit : Word → Word}
  {val : Word → Word → Word → Word} {i v : USize} {seen : UInt32} {kc : Word}

theorem keyStep_unknown (z : ScanErr) (h : bit kc = 0) : KeyStep F bit val i v seen kc (.err z) :=
  Or.inl ⟨rfl, Or.inl h⟩

theorem keyStep_guard {sb : UInt32} (hbit : bit kc = sb.toUInt64) {X : ScanRes α} {z : ScanErr}
    (hX : seen &&& sb = 0 → KeyStep F bit val i v seen kc X) :
    KeyStep F bit val i v seen kc (if seen &&& sb = 0 then X else .err z) := by
  by_cases hs : seen &&& sb = 0
  · rw [ite_eq_left hs]; exact hX hs
  · rw [ite_eq_right hs]
    refine Or.inl ⟨rfl, Or.inr (Or.inl ?_)⟩
    rw [hbit, ← UInt32.toUInt64_and]
    exact fun h => hs ((u32_toUInt64_eq_zero _).mp h)

theorem keyStep_err (z : ScanErr) (h : ¬ i.toUInt64 < val kc i.toUInt64 v.toUInt64) :
    KeyStep F bit val i v seen kc (.err z) :=
  Or.inl ⟨rfl, Or.inr (Or.inr h)⟩

theorem keyStep_lt {sb : UInt32} (hbit : bit kc = sb.toUInt64) (hsb : sb ≠ 0) (hseen : seen &&& sb = 0)
    (e : USize) (hval : i < e → val kc i.toUInt64 v.toUInt64 = e.toUInt64)
    (hval' : i.toUInt64 < val kc i.toUInt64 v.toUInt64 → i < e)
    {G : ScanRes α} {y : ScanErr} (hG : ∃ st', okW G = okW (F e false (seen ||| sb) st')) :
    KeyStep F bit val i v seen kc (if i < e then G else .err y) := by
  by_cases hie : i < e
  · rw [ite_eq_left hie]
    obtain ⟨st', hst⟩ := hG
    refine Or.inr ⟨?_, ?_, e, seen ||| sb, (hval hie).symm, (lt_toUInt64_iff _ _).mp hie, ?_, st', hst⟩
    · rw [hbit]; intro h; exact hsb ((u32_toUInt64_eq_zero _).mp h)
    · rw [hbit, ← UInt32.toUInt64_and, hseen]; rfl
    · rw [hbit, UInt32.toUInt64_or]
  · rw [ite_eq_right hie]
    exact keyStep_err y (fun h => hie (hval' h))

end keystep

section keykinds
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
variable {F : USize → Bool → UInt32 → σ → ScanRes α} {bit : Word → Word}
  {val : Word → Word → Word → Word} {i v : USize} {seen : UInt32} {kc : Word}
include h64 hsize

theorem slotNatN_link (i v : USize) :
    L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64 =
      if numEnd b v = v then 0 else if i < numEnd b v then (numEnd b v).toUInt64 else 0 := by
  unfold L.Scan.Values.slotNatN
  rw [USize.toNat_toUInt64, ← numEnd_toUInt64_eq b h64 (by omega)]
  simp only [← eq_toUInt64_iff, ← lt_toUInt64_iff]

/-- A value read by `numEnd` (`slot_nat`). -/
theorem keyStep_num {sb : UInt32} (hbit : bit kc = sb.toUInt64) (hsb : sb ≠ 0)
    (hseen : seen &&& sb = 0)
    (hval : val kc i.toUInt64 v.toUInt64 = L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64)
    {G : ScanRes α} {x y : ScanErr}
    (hG : ∃ st', okW G = okW (F (numEnd b v) false (seen ||| sb) st')) :
    KeyStep F bit val i v seen kc
      (if numEnd b v = v then .err x else if i < numEnd b v then G else .err y) := by
  have hv2 := hval.trans (slotNatN_link b h64 hsize i v)
  by_cases hn : numEnd b v = v
  · rw [ite_eq_left hn]; apply keyStep_err; rw [hv2, ite_eq_left hn]; exact UInt64.not_lt_zero
  · rw [ite_eq_right hn]
    apply keyStep_lt hbit hsb hseen _ _ _ hG
    · intro h; rw [hv2, ite_eq_right hn, ite_eq_left h]
    · intro h; rw [hv2, ite_eq_right hn] at h
      by_cases h' : i < numEnd b v
      · exact h'
      · rw [ite_eq_right h'] at h; exact absurd h UInt64.not_lt_zero

/-- A value read by a scanner that returns its end or `0` (`scanBinderInfo`). -/
theorem keyStep_usz {sb : UInt32} (hbit : bit kc = sb.toUInt64) (hsb : sb ≠ 0)
    (hseen : seen &&& sb = 0) (u : USize)
    (hval : val kc i.toUInt64 v.toUInt64 = u.toUInt64)
    {G : ScanRes α} {x y : ScanErr}
    (hG : ∃ st', okW G = okW (F u false (seen ||| sb) st')) :
    KeyStep F bit val i v seen kc (if u = 0 then .err x else if i < u then G else .err y) := by
  by_cases hn : u = 0
  · rw [ite_eq_left hn]; apply keyStep_err; rw [hval, hn]; exact UInt64.not_lt_zero
  · rw [ite_eq_right hn]
    apply keyStep_lt hbit hsb hseen _ (fun _ => hval) _ hG
    intro h; rw [hval] at h; exact (lt_toUInt64_iff _ _).mpr h

end keykinds

/-- A value read by a scanner with a `ScanRes` (the `.err` arm). -/
theorem keyStep_res_err {β : Type} {F : USize → Bool → UInt32 → σ → ScanRes α} {bit : Word → Word}
    {val : Word → Word → Word → Word} {i v : USize} {seen : UInt32} {kc : Word}
    (S : ScanRes β) (hval : val kc i.toUInt64 v.toUInt64 = okW S) (z : ScanErr) (heq : S = .err z) (z' : ScanErr) :
    KeyStep F bit val i v seen kc (.err z') := by
  apply keyStep_err; rw [hval, heq]; exact UInt64.not_lt_zero

/-- A value read by a scanner with a `ScanRes` (the `.ok` arm). -/
theorem keyStep_res_ok {β : Type} {F : USize → Bool → UInt32 → σ → ScanRes α} {bit : Word → Word}
    {val : Word → Word → Word → Word} {i v : USize} {seen : UInt32} {kc : Word} {sb : UInt32}
    (hbit : bit kc = sb.toUInt64) (hsb : sb ≠ 0) (hseen : seen &&& sb = 0)
    (S : ScanRes β) (hval : val kc i.toUInt64 v.toUInt64 = okW S) (x : β) (e : USize) (heq : S = .ok x e)
    {G : ScanRes α} {y : ScanErr}
    (hG : ∃ st', okW G = okW (F e false (seen ||| sb) st')) :
    KeyStep F bit val i v seen kc (if i < e then G else .err y) := by
  rw [heq] at hval
  apply keyStep_lt hbit hsb hseen _ (fun _ => hval) _ hG
  intro h; rw [hval] at h; exact (lt_toUInt64_iff _ _).mpr h


/-! ## The value scanners, as `val` reads them -/

section values
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem scanBoolN_le (i : Nat) (v : Bool) (p : Nat) (h : L.Scan.Lit.scanBoolN b.data i = some (v, p)) :
    p ≤ b.data.size ∧ p = i + (if v then 4 else 5) := by
  unfold L.Scan.Lit.scanBoolN at h
  have hlen : ∀ o n, o + n ≤ L.Scan.Lit.LITS.length → L.Scan.Lit.matchLitN b.data i L.Scan.Lit.LITS o n 0 = true →
      n ≤ b.data.size - i := by
    intro o n hL hm
    rw [matchLitN_eq_isPrefixOf _ _ _ _ _ _ hL LITS_ne_zero] at hm
    have := (List.isPrefixOf_iff_prefix.mp hm).length_le
    simp only [Nat.add_zero, Nat.sub_zero, List.length_take, List.length_drop, Array.length_toList] at this
    have hl : L.Scan.Lit.LITS.length = 9 := by decide
    omega
  split at h
  · next hm =>
    have := hlen 0 4 (by decide) hm
    simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    exact ⟨by omega, by simp⟩
  · split at h
    · next hm =>
      have := hlen 4 5 (by decide) hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨by omega, by simp⟩
    · simp at h

/-- `scan_bool`, as the record loops read it. -/
theorem scanBool_link (v : USize) : okW (scanBool b v) = boolEndN b.data v.toUInt64 := by
  rw [scanBool_eq_N b v (by rw [USize.size_eq_two_pow, h64]; omega)]
  unfold boolEndN
  rw [USize.toNat_toUInt64]
  cases hs : L.Scan.Lit.scanBoolN b.data v.toNat with
  | none => simp [okW, L.Scan.Lit.encBool]
  | some vp =>
    obtain ⟨x, p⟩ := vp
    have hp := scanBoolN_le b h64 hsize _ _ _ hs
    have hbs : b.data.size = b.size := rfl
    simp only [okW, L.Scan.Lit.encBool, List.headD_cons, List.tail_cons]
    simp only [show ((1 : Word) = 0) = False from by decide, ite_false]
    have hU : UInt64.size = 2 ^ 64 := rfl
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (by rw [hU]; omega), USize.toNat_toUInt64, USize.toNat_add]
    have hU' := usize_size_eq64 h64
    cases x <;> simp only [ite_true, Bool.false_eq_true, ite_false] at hp ⊢ <;>
      simp only [USize.toNat_ofNat, hU'] <;> omega

omit h64 hsize in
theorem okW_strLink {β : Type} (r : ScanRes β) : StrLink.okW r = okW r := by cases r <;> rfl

/-- `scan_string`, as the record loops read it (`StrLink.scanString_eq`). -/
@[refines_part ConLeche.Frontend.scanString "validity"]
theorem scanString_link (v : USize) :
    okW (scanString b v) = L.Scan.Str.scanStringN b.data v.toUInt64 := by
  rw [← okW_strLink]; exact StrLink.scanString_eq h64 b hsize v

/-- `scan_binder_info` (`ValuesLink`). -/
@[refines_part ConLeche.Frontend.scanBinderInfo "validity"]
theorem scanBinderInfo_link (v : USize) :
    (scanBinderInfo b v).toUInt64 = L.Scan.Values.binderInfoN b.data v.toUInt64 :=
  scanBinderInfo_eq_binderInfoN b h64 hsize v

/-- `scan_hints` (`ValuesLink`). -/
@[refines_part ConLeche.Frontend.scanHints "validity"]
theorem scanHints_link (v : USize) : okW (scanHints b v) = L.Scan.Values.hintsN b.data v.toUInt64 :=
  scanHints_eq_hintsN b h64 hsize v

/-- `ScanRes (List Nat)` as the model's `(end, count)`. -/
def encNL : ScanRes (List Nat) → Word × Word
  | .ok us p => (p.toUInt64, UInt64.ofNat us.length)
  | .err _ => (0, 0)

omit h64 hsize in
theorem digit_iff (c : UInt8) : isDigit c = true ↔ (48 ≤ c.toUInt64 ∧ c.toUInt64 ≤ 57) := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
    UInt64.le_iff_toNat_le, UInt8.toNat_toUInt64]
  rfl

/-- `scanNatListLoop` against `natListN`: the end and the number of items. -/
theorem natListLoop_link (i : USize) (acc : List Nat) (w : Bool) (hacc : acc.length ≤ i.toNat) :
    encNL (scanNatListLoop b i acc w) =
      L.Scan.Values.natListN b.data i.toUInt64 (UInt64.ofNat acc.length) (bw w) := by
  rw [scanNatListLoop, L.Scan.Values.natListN]
  by_cases h : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp h
    have hcw := byteW_eq b h64 hsize i
    have hs := succ_toUInt64 b h64 hsize i
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i h
    have hin := usizeInBounds b i h
    rw [dite_eq_left h, dite_eq_left hlt]
    simp only [uget_byteAt _ i h, hcw]
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, (ws_iff _).mp hws, ite_true]
      rw [natListLoop_link (i + 1) acc w (by omega), hs]
    have hws' : ¬ ((byteAt b i).toUInt64 = 32 ∨ (byteAt b i).toUInt64 = 9 ∨
        (byteAt b i).toUInt64 = 13) := by rw [← ws_iff]; exact hws
    simp only [hws, hws', ite_false, Bool.false_eq_true]
    by_cases h93 : byteAt b i = 93
    · have hU : UInt64.size = 2 ^ 64 := rfl
      have hz : UInt64.ofNat acc.length = 0 ↔ acc = [] := by
        rw [← List.length_eq_zero_iff, ← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' (by rw [hU]; omega)]; rfl
      simp only [h93, show ((93 : UInt8) == 93) = true from rfl, show (93 : UInt8).toUInt64 = 93 from rfl,
        ite_true, bw_ne_zero, ne_eq, hz]
      by_cases hw : w = true ∧ ¬ acc = []
      · have he : acc.isEmpty = false := by cases acc <;> simp_all
        simp only [hw, he]; rfl
      · rw [ite_eq_right hw, ite_eq_right (by
          simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff]; exact hw)]
        simp [encNL, hs]
    have h93' : ¬ (byteAt b i).toUInt64 = 93 := fun h' => h93 ((u8_toUInt64_eq _ 93 (by decide)).mp h')
    simp only [h93', show ¬ (byteAt b i == 93) = true by simpa using h93, ite_false]
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, show (44 : UInt8).toUInt64 = 44 from rfl,
        ite_true, bw_ne_zero, ne_eq]
      by_cases hw : w = true
      · simp only [hw, ite_true]; rfl
      · simp only [hw, ite_false, Bool.false_eq_true]
        rw [natListLoop_link (i + 1) acc true (by omega), hs]; rfl
    have h44' : ¬ (byteAt b i).toUInt64 = 44 := fun h' => h44 ((u8_toUInt64_eq _ 44 (by decide)).mp h')
    simp only [h44', show ¬ (byteAt b i == 44) = true by simpa using h44, ite_false]
    by_cases hd : isDigit (byteAt b i) = true
    · simp only [hd, (digit_iff _).mp hd, and_self, ite_true]
      by_cases hw : w = true
      · subst hw
        simp only [bw, ite_true, Bool.not_true, Bool.false_eq_true, ite_false,
          show ¬ ((1 : Word) = 0) from by decide]
        have hne := numEnd_toUInt64_eq b h64 (by omega) i
        simp only [USize.toNat_toUInt64]
        rw [← hne]
        by_cases he : numEnd b i = i
        · simp only [he, beq_self_eq_true, ite_true]; rfl
        have he' : ¬ (numEnd b i).toUInt64 = i.toUInt64 := fun h' => he ((eq_toUInt64_iff _ _).mpr h')
        simp only [he', show (numEnd b i == i) = false by simpa using he, Bool.false_eq_true, ite_false]
        by_cases hie : i < numEnd b i
        · rw [dite_eq_left hie, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          have hie' := USize.lt_iff_toNat_lt.mp hie
          rw [natListLoop_link (numEnd b i) (readNatAt b i (numEnd b i) :: acc) false (by simp only [List.length_cons]; omega)]
          congr 1
          simp [UInt64.ofNat_add]
        · rw [dite_eq_right hie, ite_eq_right (fun h' => hie ((lt_toUInt64_iff _ _).mpr h'))]; rfl
      · have hw' : w = false := by simpa using hw
        subst hw'
        simp [bw, encNL]
    · have hd' : ¬ (48 ≤ (byteAt b i).toUInt64 ∧ (byteAt b i).toUInt64 ≤ 57) := by
        rw [← digit_iff]; exact hd
      simp only [hd, hd', ite_false, Bool.false_eq_true]; rfl
  · rw [dite_eq_right h, dite_eq_right (by rw [← lt_usize_iff b h64 hsize]; exact h)]; rfl
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp hie; omega)

/-- `scanNatList` against `natListEntryN` (the content of `ValuesLink.scanNatList_eq_natListEntryN`). -/
theorem natList_link (i : USize) :
    encNL (scanNatList b i) = L.Scan.Values.natListEntryN b.data i.toUInt64 := by
  unfold scanNatList L.Scan.Values.natListEntryN
  by_cases h : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp h
    by_cases hc : byteAt b i = 91
    · rw [ite_eq_left (by simp [hc]), ite_eq_left ⟨hlt, by rw [byteW_eq b h64 hsize, hc]; rfl⟩,
        natListLoop_link b h64 hsize (i + 1) [] true (by simp), succ_toUInt64 b h64 hsize]; rfl
    · rw [ite_eq_right (by simp [hc]), ite_eq_right (fun h' => hc ((u8_toUInt64_eq _ 91 (by decide)).mp
        (by rw [← byteW_eq b h64 hsize]; exact h'.2)))]; rfl
  · have h0 : byteAt b i = 0 := by unfold byteAt; rw [dite_eq_right h]
    rw [ite_eq_right (by simp [h0]), ite_eq_right (fun h' => h ((lt_usize_iff b h64 hsize i).mpr h'.1))]; rfl

/-- `scan_nat_list`, its end. -/
@[refines_part ConLeche.Frontend.scanNatList "validity"]
theorem scanNatList_link (v : USize) :
    okW (scanNatList b v) = (L.Scan.Values.natListEntryN b.data v.toUInt64).1 := by
  rw [← natList_link b h64 hsize v]
  cases scanNatList b v <;> rfl

end values

/-! ## Entering a record -/

section entry
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem entry_link {L : ScanRes α} {z : ScanErr} {M : Word} (i : USize) (c : UInt8) (n : Nat)
    (hn : n < 256) (hc : c = OfNat.ofNat n) (hc0 : n ≠ 0) (hL : okW L = M) :
    okW (if (byteAt b i == c) = true then L else .err z) =
      if i.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data i.toUInt64 = OfNat.ofNat n then M
      else 0 := by
  subst hc
  by_cases h : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp h
    by_cases hb : byteAt b i = OfNat.ofNat n
    · have hb' : byteW b.data i.toUInt64 = OfNat.ofNat n := by
        rw [byteW_eq b h64 hsize]; exact (u8_toUInt64_eq _ n hn).mpr hb
      rw [ite_eq_left (by simp [hb]), ite_eq_left ⟨hlt, hb'⟩, hL]
    · have hb' : byteW b.data i.toUInt64 ≠ OfNat.ofNat n := by
        rw [byteW_eq b h64 hsize]; exact fun h' => hb ((u8_toUInt64_eq _ n hn).mp h')
      rw [ite_eq_right (by simp [hb]), ite_eq_right (fun h' => hb' h'.2)]; rfl
  · have h0 : byteAt b i = 0 := by unfold byteAt; rw [dite_eq_right h]
    have hb : ¬ byteAt b i = OfNat.ofNat n := by
      rw [h0]; intro h'
      have := congrArg UInt8.toNat h'
      simp only [UInt8.toNat_ofNat] at this
      omega
    rw [ite_eq_right (by simp [hb]), ite_eq_right (fun h' => h ((lt_usize_iff b h64 hsize i).mpr h'.1))]; rfl

end entry

/-! ## The generic list of objects -/

variable {β : Type}

/-- The shape of a con-leche list-of-objects loop `F` (`scan*ListLoop`) reading items with
`item` (the model of `scan*`). -/
structure ListLoop (b : ByteArray) (F : USize → List β → Bool → ScanRes (List β))
    (item : Word → Word) : Prop where
  stop : ∀ i acc w, ¬ i < b.usize → okW (F i acc w) = 0
  ws : ∀ i acc w, i < b.usize → isWs (byteAt b i) = true → F i acc w = F (i + 1) acc w
  close : ∀ i acc w, i < b.usize → byteAt b i = 93 →
    okW (F i acc w) = if w = true ∧ acc ≠ [] then 0 else (i + 1).toUInt64
  comma : ∀ i acc w, i < b.usize → byteAt b i = 44 →
    okW (F i acc w) = if w = true then 0 else okW (F (i + 1) acc true)
  openw : ∀ i acc, i < b.usize → byteAt b i = 123 → okW (F i acc false) = 0
  item : ∀ i acc, i < b.usize → byteAt b i = 123 →
    (okW (F i acc true) = 0 ∧ ¬ i.toUInt64 < item i.toUInt64) ∨
    (∃ e x, e.toUInt64 = item i.toUInt64 ∧ i.toUInt64 < e.toUInt64 ∧
      okW (F i acc true) = okW (F e (x :: acc) false))
  other : ∀ i acc w, i < b.usize → isWs (byteAt b i) = false → byteAt b i ≠ 93 →
    byteAt b i ≠ 44 → byteAt b i ≠ 123 → okW (F i acc w) = 0

theorem listItem_err {F : USize → List β → Bool → ScanRes (List β)} {item : Word → Word}
    {γ : Type} {i : USize} {acc : List β} (S : ScanRes γ) (hval : item i.toUInt64 = okW S)
    (z : ScanErr) (heq : S = .err z) (z' : ScanErr) :
    (okW (.err z' : ScanRes (List β)) = 0 ∧ ¬ i.toUInt64 < item i.toUInt64) ∨
    (∃ e x, e.toUInt64 = item i.toUInt64 ∧ i.toUInt64 < e.toUInt64 ∧
      okW (.err z' : ScanRes (List β)) = okW (F e (x :: acc) false)) := by
  refine Or.inl ⟨rfl, ?_⟩
  rw [hval, heq]; exact UInt64.not_lt_zero

theorem listItem_ok {F : USize → List β → Bool → ScanRes (List β)} {item : Word → Word}
    {i : USize} {acc : List β} (S : ScanRes β) (hval : item i.toUInt64 = okW S)
    (x : β) (e : USize) (heq : S = .ok x e) (z' : ScanErr) :
    (okW (if i < e then F e (x :: acc) false else .err z') = 0 ∧ ¬ i.toUInt64 < item i.toUInt64) ∨
    (∃ e' x', e'.toUInt64 = item i.toUInt64 ∧ i.toUInt64 < e'.toUInt64 ∧
      okW (if i < e then F e (x :: acc) false else .err z') = okW (F e' (x' :: acc) false)) := by
  rw [heq] at hval
  by_cases hie : i < e
  · rw [ite_eq_left hie]
    exact Or.inr ⟨e, x, hval.symm, (lt_toUInt64_iff _ _).mp hie, rfl⟩
  · rw [ite_eq_right hie]
    refine Or.inl ⟨rfl, ?_⟩
    rw [hval]; exact fun h => hie ((lt_toUInt64_iff _ _).mpr h)

section genericList
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem objListN_link (F : USize → List β → Bool → ScanRes (List β)) (item : Word → Word)
    (H : ListLoop b F item) (i : USize) (acc : List β) (w : Bool) (hacc : acc.length ≤ i.toNat) :
    okW (F i acc w) = objListN item b.data i.toUInt64 (UInt64.ofNat acc.length) (bw w) := by
  by_cases h : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp h
    have hcw := byteW_eq b h64 hsize i
    have hs := succ_toUInt64 b h64 hsize i
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i h
    have hin := usizeInBounds b i h
    by_cases hws : isWs (byteAt b i) = true
    · rw [H.ws i acc w h hws, objListN_ws _ _ _ _ _ hlt (by rw [hcw]; exact (ws_iff _).mp hws),
        objListN_link F item H (i + 1) acc w (by omega), hs]
    have hws' : ¬ (byteW b.data i.toUInt64 = 32 ∨ byteW b.data i.toUInt64 = 9 ∨
        byteW b.data i.toUInt64 = 13) := by rw [hcw, ← ws_iff]; exact hws
    by_cases h93 : byteAt b i = 93
    · have h93' : byteW b.data i.toUInt64 = 93 := by rw [hcw, h93]; rfl
      rw [H.close i acc w h h93, objListN_close _ _ _ _ _ hlt hws' h93', hs]
      have hz : UInt64.ofNat acc.length = 0 ↔ acc = [] := by
        have hU : UInt64.size = 2 ^ 64 := rfl
        rw [← List.length_eq_zero_iff, ← UInt64.toNat_inj, UInt64.toNat_ofNat_of_lt' (by rw [hU]; omega)]; rfl
      simp only [bw_ne_zero, ne_eq, hz]
    have h93' : byteW b.data i.toUInt64 ≠ 93 := by
      rw [hcw]; exact fun h' => h93 ((u8_toUInt64_eq _ 93 (by decide)).mp h')
    by_cases h44 : byteAt b i = 44
    · have h44' : byteW b.data i.toUInt64 = 44 := by rw [hcw, h44]; rfl
      rw [H.comma i acc w h h44, objListN_comma _ _ _ _ _ hlt hws' h93' h44']
      by_cases hw : w = true
      · rw [ite_eq_left hw, ite_eq_left ((bw_ne_zero w).mpr hw)]
      · rw [ite_eq_right hw, ite_eq_right (by rw [bw_ne_zero]; exact hw),
          objListN_link F item H (i + 1) acc true (by omega), hs]; rfl
    have h44' : byteW b.data i.toUInt64 ≠ 44 := by
      rw [hcw]; exact fun h' => h44 ((u8_toUInt64_eq _ 44 (by decide)).mp h')
    by_cases h123 : byteAt b i = 123
    · have h123' : byteW b.data i.toUInt64 = 123 := by rw [hcw, h123]; rfl
      rw [objListN_open _ _ _ _ _ hlt hws' h93' h44' h123']
      cases w with
      | false => rw [H.openw i acc h h123]; rfl
      | true =>
        rw [ite_eq_right (by decide : ¬ bw true = 0)]
        rcases H.item i acc h h123 with ⟨hr, hn⟩ | ⟨e, x, he, hie, hr⟩
        · rw [hr, ite_eq_right hn]
        · have hie' : i.toNat < e.toNat := by
            rw [UInt64.lt_iff_toNat_lt, USize.toNat_toUInt64, USize.toNat_toUInt64] at hie; exact hie
          have heU : e.toNat < 2 ^ 64 := by rw [← usize_size_eq64 h64]; exact e.toNat_lt_size
          rw [hr, ← he, ite_eq_left hie,
            objListN_link F item H e (x :: acc) false (by simp only [List.length_cons]; omega)]
          congr 1
          simp [UInt64.ofNat_add]
    · have h123' : byteW b.data i.toUInt64 ≠ 123 := by
        rw [hcw]; exact fun h' => h123 ((u8_toUInt64_eq _ 123 (by decide)).mp h')
      rw [H.other i acc w h (by simpa using hws) h93 h44 h123,
        objListN_other _ _ _ _ _ hlt hws' h93' h44' h123']
  · rw [H.stop i acc w h, objListN_end]
    rw [← lt_usize_iff b h64 hsize]; exact h
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (rw [UInt64.lt_iff_toNat_lt, USize.toNat_toUInt64, USize.toNat_toUInt64] at hie; omega)

end genericList


/-! ## The tactics every record shares -/

/-- `∃ st', okW G = okW (F e false s st')`, `F` a loop over the tuple of its fields. -/
syntax "tuple_ex" : tactic
macro_rules
  | `(tactic| tuple_ex) => `(tactic| first
      | exact ⟨(_, _), rfl⟩ | exact ⟨(_, _, _), rfl⟩ | exact ⟨(_, _, _, _), rfl⟩
      | exact ⟨(_, _, _, _, _), rfl⟩ | exact ⟨(_, _, _, _, _, _), rfl⟩
      | exact ⟨(_, _, _, _, _, _, _), rfl⟩ | exact ⟨(_, _, _, _, _, _, _, _), rfl⟩
      | exact ⟨(_, _, _, _, _, _, _, _, _), rfl⟩ | exact ⟨(_, _, _, _, _, _, _, _, _, _), rfl⟩)

/-- `val k ks v = okW (scanner b v)` (or `item i = okW (scanner b i)`): a value link, then the
key's arm of `val` by evaluation. Extended below by every link proved. -/
syntax "link_val" : tactic
macro_rules | `(tactic| link_val) => `(tactic| (rw [scanBool_link _ ‹_› ‹_›]) <;> rfl)
macro_rules | `(tactic| link_val) => `(tactic| (rw [scanString_link _ ‹_› ‹_›]) <;> rfl)
macro_rules | `(tactic| link_val) => `(tactic| (rw [scanBinderInfo_link _ ‹_› ‹_›]) <;> rfl)
macro_rules | `(tactic| link_val) => `(tactic| (rw [scanHints_link _ ‹_› ‹_›]) <;> rfl)
macro_rules | `(tactic| link_val) => `(tactic| (rw [scanNatList_link _ ‹_› ‹_›]) <;> rfl)

/-- One key arm of a record loop, after `keyStep_guard`'s duplicate check. -/
syntax "key_value " ident : tactic
macro_rules
  | `(tactic| key_value $hs) => `(tactic| first
      | (apply keyStep_num _ ‹_› ‹_› (by decide) (by decide) $hs rfl; tuple_ex)
      | (apply keyStep_usz _ ‹_› ‹_› (by decide) (by decide) $hs _ (by link_val); tuple_ex)
      | (split
         all_goals first
           | (rename_i heq; exact keyStep_res_err _ (by link_val) _ heq _)
           | (rename_i heq
              apply keyStep_res_ok (by decide) (by decide) $hs _ (by link_val) _ _ heq
              tuple_ex)))

/-- `ObjLoop b (fun i w seen st => f b i w seen st.1 …) mask bit val` for con-leche's record
loop `f`: the six arms by unfolding, the key arm key by key. -/
syntax "obj_loop " ident ident : tactic
macro_rules
  | `(tactic| obj_loop $f $b) => `(tactic| (
    constructor
    · intro i w seen st h; rw [$f:ident, dif_neg h]; rfl
    · intro i w seen st h hws; rw [$f:ident, dif_pos h]; simp only [uget_byteAt _ i h, hws, if_true]
    · intro i w seen st h hc; rw [$f:ident, dif_pos h]; simp [uget_byteAt _ i h, hc, isWs]
      (repeat' split) <;> simp_all [okW]
    · intro i w seen st h hc; rw [$f:ident, dif_pos h]; simp [uget_byteAt _ i h, hc, isWs]
      (repeat' split) <;> simp_all [okW]
    · intro i w seen st h hc hbad; rw [$f:ident, dif_pos h]; simp [uget_byteAt _ i h, hc, isWs]
      (repeat' split) <;> simp_all [okW]
    · intro i seen h hc hk hv; simp only [Prod.forall]; intros; rw [$f:ident, dif_pos h]
      simp [uget_byteAt _ i h, hc, isWs, hk, hv]
      generalize valueAt $b i (keyEnd $b (i + 1)) = v
      generalize keyAt $b i (keyEnd $b (i + 1) - (i + 1)) = K
      cases K
      all_goals dsimp only
      all_goals first
        | exact keyStep_unknown _ (by decide)
        | (apply keyStep_guard (by decide)
           intro hseen
           key_value hseen)
    · intro i w seen st h hws h1 h2 h3; rw [$f:ident, dif_pos h]
      simp [uget_byteAt _ i h, hws, h1, h2, h3]; rfl))

/-- `ListLoop b (f b) item` for con-leche's list loop `f`. -/
syntax "list_loop " ident : tactic
macro_rules
  | `(tactic| list_loop $f) => `(tactic| (
    constructor
    · intro i acc w h; rw [$f:ident, dif_neg h]; rfl
    · intro i acc w h hws; rw [$f:ident, dif_pos h]; simp only [uget_byteAt _ i h, hws, if_true]
    · intro i acc w h hc; rw [$f:ident, dif_pos h]; simp [uget_byteAt _ i h, hc, isWs]
      (repeat' split) <;> simp_all [okW]
    · intro i acc w h hc; rw [$f:ident, dif_pos h]; simp [uget_byteAt _ i h, hc, isWs]
      (repeat' split) <;> simp_all [okW]
    · intro i acc h hc; rw [$f:ident, dif_pos h]; simp [uget_byteAt _ i h, hc, isWs]; rfl
    · intro i acc h hc; rw [$f:ident, dif_pos h]
      simp (config := {decide := true}) only [uget_byteAt _ i h, hc, ↓reduceIte, dite_eq_ite]
      split
      all_goals first
        | (rename_i heq; exact listItem_err _ (by link_val) _ heq _)
        | (rename_i heq; exact listItem_ok _ (by link_val) _ _ heq _)
    · intro i acc w h hws h1 h2 h3; rw [$f:ident, dif_pos h]
      simp [uget_byteAt _ i h, hws, h1, h2, h3]; rfl))

/-! ## The records, bottom-up -/

section records
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- con-leche's `scanStrNameLoop`. -/
theorem strNameLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : String) :
    okW (ConLeche.Frontend.scanStrNameLoop b i w seen a0 a1) =
      objN strNameBit (strNameVal b.data) 3 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × String) => ConLeche.Frontend.scanStrNameLoop b i w seen st.1 st.2)
    3 strNameBit (strNameVal b.data) (by obj_loop ConLeche.Frontend.scanStrNameLoop b) i w seen (a0, a1)

/-- con-leche's `scanStrName`. -/
@[refines_part ConLeche.Frontend.scanStrName "validity"]
theorem strName_link (i : USize) : okW (ConLeche.Frontend.scanStrName b i) = strNameN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanStrName strNameN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (strNameLoop_link b h64 hsize (i + 1) true 0 0 "")]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [strName_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanNumNameLoop`. -/
theorem numNameLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) :
    okW (ConLeche.Frontend.scanNumNameLoop b i w seen a0 a1) =
      objN numNameBit (numNameVal b.data) 3 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat) => ConLeche.Frontend.scanNumNameLoop b i w seen st.1 st.2)
    3 numNameBit (numNameVal b.data) (by obj_loop ConLeche.Frontend.scanNumNameLoop b) i w seen (a0, a1)

/-- con-leche's `scanNumName`. -/
@[refines_part ConLeche.Frontend.scanNumName "validity"]
theorem numName_link (i : USize) : okW (ConLeche.Frontend.scanNumName b i) = numNameN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanNumName numNameN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (numNameLoop_link b h64 hsize (i + 1) true 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [numName_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanAppExprLoop`. -/
theorem appLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) :
    okW (ConLeche.Frontend.scanAppExprLoop b i w seen a0 a1) =
      objN appBit (appVal b.data) 3 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat) => ConLeche.Frontend.scanAppExprLoop b i w seen st.1 st.2)
    3 appBit (appVal b.data) (by obj_loop ConLeche.Frontend.scanAppExprLoop b) i w seen (a0, a1)

/-- con-leche's `scanAppExpr`. -/
@[refines_part ConLeche.Frontend.scanAppExpr "validity"]
theorem app_link (i : USize) : okW (ConLeche.Frontend.scanAppExpr b i) = appN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanAppExpr appN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (appLoop_link b h64 hsize (i + 1) true 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [app_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanLamExprLoop`. -/
theorem lamLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) :
    okW (ConLeche.Frontend.scanLamExprLoop b i w seen a0 a1) =
      objN binderBit (binderVal b.data) 15 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat) => ConLeche.Frontend.scanLamExprLoop b i w seen st.1 st.2)
    15 binderBit (binderVal b.data) (by obj_loop ConLeche.Frontend.scanLamExprLoop b) i w seen (a0, a1)

/-- con-leche's `scanLamExpr`. -/
@[refines_part ConLeche.Frontend.scanLamExpr "validity"]
theorem lam_link (i : USize) : okW (ConLeche.Frontend.scanLamExpr b i) = binderN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanLamExpr binderN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (lamLoop_link b h64 hsize (i + 1) true 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [lam_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanForallExprLoop`. -/
theorem forallLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) :
    okW (ConLeche.Frontend.scanForallExprLoop b i w seen a0 a1) =
      objN binderBit (binderVal b.data) 15 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat) => ConLeche.Frontend.scanForallExprLoop b i w seen st.1 st.2)
    15 binderBit (binderVal b.data) (by obj_loop ConLeche.Frontend.scanForallExprLoop b) i w seen (a0, a1)

/-- con-leche's `scanForallExpr`. -/
@[refines_part ConLeche.Frontend.scanForallExpr "validity"]
theorem forall_link (i : USize) : okW (ConLeche.Frontend.scanForallExpr b i) = binderN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanForallExpr binderN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (forallLoop_link b h64 hsize (i + 1) true 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [forall_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanLetExprLoop`. -/
theorem letELoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) (a2 : Nat) :
    okW (ConLeche.Frontend.scanLetExprLoop b i w seen a0 a1 a2) =
      objN letEBit (letEVal b.data) 27 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat × Nat) => ConLeche.Frontend.scanLetExprLoop b i w seen st.1 st.2.1 st.2.2)
    27 letEBit (letEVal b.data) (by obj_loop ConLeche.Frontend.scanLetExprLoop b) i w seen (a0, a1, a2)

/-- con-leche's `scanLetExpr`. -/
@[refines_part ConLeche.Frontend.scanLetExpr "validity"]
theorem letE_link (i : USize) : okW (ConLeche.Frontend.scanLetExpr b i) = letEN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanLetExpr letEN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (letELoop_link b h64 hsize (i + 1) true 0 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [letE_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanConstExprLoop`. -/
theorem constELoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : List Nat) :
    okW (ConLeche.Frontend.scanConstExprLoop b i w seen a0 a1) =
      objN constEBit (constEVal b.data) 3 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × List Nat) => ConLeche.Frontend.scanConstExprLoop b i w seen st.1 st.2)
    3 constEBit (constEVal b.data) (by obj_loop ConLeche.Frontend.scanConstExprLoop b) i w seen (a0, a1)

/-- con-leche's `scanConstExpr`. -/
@[refines_part ConLeche.Frontend.scanConstExpr "validity"]
theorem constE_link (i : USize) : okW (ConLeche.Frontend.scanConstExpr b i) = constEN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanConstExpr constEN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (constELoop_link b h64 hsize (i + 1) true 0 0 [])]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [constE_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanProjExprLoop`. -/
theorem projLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) (a2 : Nat) :
    okW (ConLeche.Frontend.scanProjExprLoop b i w seen a0 a1 a2) =
      objN projBit (projVal b.data) 7 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat × Nat) => ConLeche.Frontend.scanProjExprLoop b i w seen st.1 st.2.1 st.2.2)
    7 projBit (projVal b.data) (by obj_loop ConLeche.Frontend.scanProjExprLoop b) i w seen (a0, a1, a2)

/-- con-leche's `scanProjExpr`. -/
@[refines_part ConLeche.Frontend.scanProjExpr "validity"]
theorem proj_link (i : USize) : okW (ConLeche.Frontend.scanProjExpr b i) = projN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanProjExpr projN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (projLoop_link b h64 hsize (i + 1) true 0 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [proj_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanRuleLoop`. -/
theorem ruleLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Nat) (a1 : Nat) (a2 : Nat) :
    okW (ConLeche.Frontend.scanRuleLoop b i w seen a0 a1 a2) =
      objN ruleBit (ruleVal b.data) 7 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Nat × Nat × Nat) => ConLeche.Frontend.scanRuleLoop b i w seen st.1 st.2.1 st.2.2)
    7 ruleBit (ruleVal b.data) (by obj_loop ConLeche.Frontend.scanRuleLoop b) i w seen (a0, a1, a2)

/-- con-leche's `scanRule`. -/
@[refines_part ConLeche.Frontend.scanRule "validity"]
theorem rule_link (i : USize) : okW (ConLeche.Frontend.scanRule b i) = ruleN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanRule ruleN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (ruleLoop_link b h64 hsize (i + 1) true 0 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [rule_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanRuleListLoop`. -/
theorem rulesLoop_link (i : USize) (acc : List RuleRec) (w : Bool) (hacc : acc.length ≤ i.toNat) :
    okW (ConLeche.Frontend.scanRuleListLoop b i acc w) =
      objListN (ruleN b.data) b.data i.toUInt64 (UInt64.ofNat acc.length) (bw w) :=
  objListN_link b h64 hsize (ConLeche.Frontend.scanRuleListLoop b) (ruleN b.data) (by list_loop ConLeche.Frontend.scanRuleListLoop) i acc w hacc

/-- con-leche's `scanRules`. -/
@[refines_part ConLeche.Frontend.scanRules "validity"]
theorem rules_link (i : USize) : okW (ConLeche.Frontend.scanRules b i) = rulesN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanRules rulesN objListEntryN
  rw [entry_link b h64 hsize i 91 91 (by decide) rfl (by decide)
    (rulesLoop_link b h64 hsize (i + 1) [] true (by simp)), succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [rules_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndRecLoop`. -/
theorem indRecLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Bool) (a1 : Bool) (a2 : List Nat) (a3 : Nat) (a4 : Nat) (a5 : Nat) (a6 : Nat) (a7 : Nat) (a8 : List RuleRec) (a9 : Nat) :
    okW (ConLeche.Frontend.scanIndRecLoop b i w seen a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) =
      objN indRecBit (indRecVal b.data) 2046 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Bool × Bool × List Nat × Nat × Nat × Nat × Nat × Nat × List RuleRec × Nat) => ConLeche.Frontend.scanIndRecLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2.1 st.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2.2.2)
    2046 indRecBit (indRecVal b.data) (by obj_loop ConLeche.Frontend.scanIndRecLoop b) i w seen (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9)

/-- con-leche's `scanIndRec`. -/
@[refines_part ConLeche.Frontend.scanIndRec "validity"]
theorem indRec_link (i : USize) : okW (ConLeche.Frontend.scanIndRec b i) = indRecN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndRec indRecN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (indRecLoop_link b h64 hsize (i + 1) true 0 false false _ 0 0 0 0 0 _ 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indRec_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndRecListLoop`. -/
theorem indRecsLoop_link (i : USize) (acc : List IndRecRec) (w : Bool) (hacc : acc.length ≤ i.toNat) :
    okW (ConLeche.Frontend.scanIndRecListLoop b i acc w) =
      objListN (indRecN b.data) b.data i.toUInt64 (UInt64.ofNat acc.length) (bw w) :=
  objListN_link b h64 hsize (ConLeche.Frontend.scanIndRecListLoop b) (indRecN b.data) (by list_loop ConLeche.Frontend.scanIndRecListLoop) i acc w hacc

/-- con-leche's `scanIndRecs`. -/
@[refines_part ConLeche.Frontend.scanIndRecs "validity"]
theorem indRecs_link (i : USize) : okW (ConLeche.Frontend.scanIndRecs b i) = indRecsN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndRecs indRecsN objListEntryN
  rw [entry_link b h64 hsize i 91 91 (by decide) rfl (by decide)
    (indRecsLoop_link b h64 hsize (i + 1) [] true (by simp)), succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indRecs_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndTypeLoop`. -/
theorem indTypeLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : List Nat) (a1 : Bool) (a2 : Bool) (a3 : Bool) (a4 : List Nat) (a5 : Nat) (a6 : Nat) (a7 : Nat) (a8 : Nat) (a9 : Nat) :
    okW (ConLeche.Frontend.scanIndTypeLoop b i w seen a0 a1 a2 a3 a4 a5 a6 a7 a8 a9) =
      objN indTypeBit (indTypeVal b.data) 2046 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : List Nat × Bool × Bool × Bool × List Nat × Nat × Nat × Nat × Nat × Nat) => ConLeche.Frontend.scanIndTypeLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2.1 st.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2.2.2)
    2046 indTypeBit (indTypeVal b.data) (by obj_loop ConLeche.Frontend.scanIndTypeLoop b) i w seen (a0, a1, a2, a3, a4, a5, a6, a7, a8, a9)

/-- con-leche's `scanIndType`. -/
@[refines_part ConLeche.Frontend.scanIndType "validity"]
theorem indType_link (i : USize) : okW (ConLeche.Frontend.scanIndType b i) = indTypeN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndType indTypeN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (indTypeLoop_link b h64 hsize (i + 1) true 0 _ false false false _ 0 0 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indType_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndTypeListLoop`. -/
theorem indTypesLoop_link (i : USize) (acc : List IndTypeRec) (w : Bool) (hacc : acc.length ≤ i.toNat) :
    okW (ConLeche.Frontend.scanIndTypeListLoop b i acc w) =
      objListN (indTypeN b.data) b.data i.toUInt64 (UInt64.ofNat acc.length) (bw w) :=
  objListN_link b h64 hsize (ConLeche.Frontend.scanIndTypeListLoop b) (indTypeN b.data) (by list_loop ConLeche.Frontend.scanIndTypeListLoop) i acc w hacc

/-- con-leche's `scanIndTypes`. -/
@[refines_part ConLeche.Frontend.scanIndTypes "validity"]
theorem indTypes_link (i : USize) : okW (ConLeche.Frontend.scanIndTypes b i) = indTypesN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndTypes indTypesN objListEntryN
  rw [entry_link b h64 hsize i 91 91 (by decide) rfl (by decide)
    (indTypesLoop_link b h64 hsize (i + 1) [] true (by simp)), succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indTypes_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndCtorLoop`. -/
theorem indCtorLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Bool) (a1 : List Nat) (a2 : Nat) (a3 : Nat) (a4 : Nat) (a5 : Nat) (a6 : Option Nat) (a7 : Option Nat) :
    okW (ConLeche.Frontend.scanIndCtorLoop b i w seen a0 a1 a2 a3 a4 a5 a6 a7) =
      objN indCtorBit (indCtorVal b.data) 252 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Bool × List Nat × Nat × Nat × Nat × Nat × Option Nat × Option Nat) => ConLeche.Frontend.scanIndCtorLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2.1 st.2.2.2.2.2.2.1 st.2.2.2.2.2.2.2)
    252 indCtorBit (indCtorVal b.data) (by obj_loop ConLeche.Frontend.scanIndCtorLoop b) i w seen (a0, a1, a2, a3, a4, a5, a6, a7)

/-- con-leche's `scanIndCtor`. -/
@[refines_part ConLeche.Frontend.scanIndCtor "validity"]
theorem indCtor_link (i : USize) : okW (ConLeche.Frontend.scanIndCtor b i) = indCtorN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndCtor indCtorN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (indCtorLoop_link b h64 hsize (i + 1) true 0 false _ 0 0 0 0 _ _)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indCtor_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndCtorListLoop`. -/
theorem indCtorsLoop_link (i : USize) (acc : List IndCtorRec) (w : Bool) (hacc : acc.length ≤ i.toNat) :
    okW (ConLeche.Frontend.scanIndCtorListLoop b i acc w) =
      objListN (indCtorN b.data) b.data i.toUInt64 (UInt64.ofNat acc.length) (bw w) :=
  objListN_link b h64 hsize (ConLeche.Frontend.scanIndCtorListLoop b) (indCtorN b.data) (by list_loop ConLeche.Frontend.scanIndCtorListLoop) i acc w hacc

/-- con-leche's `scanIndCtors`. -/
@[refines_part ConLeche.Frontend.scanIndCtors "validity"]
theorem indCtors_link (i : USize) : okW (ConLeche.Frontend.scanIndCtors b i) = indCtorsN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndCtors indCtorsN objListEntryN
  rw [entry_link b h64 hsize i 91 91 (by decide) rfl (by decide)
    (indCtorsLoop_link b h64 hsize (i + 1) [] true (by simp)), succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indCtors_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanAxiomDeclLoop`. -/
theorem axiomDLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Bool) (a1 : List Nat) (a2 : Nat) (a3 : Nat) :
    okW (ConLeche.Frontend.scanAxiomDeclLoop b i w seen a0 a1 a2 a3) =
      objN axiomDBit (axiomDVal b.data) 15 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Bool × List Nat × Nat × Nat) => ConLeche.Frontend.scanAxiomDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2)
    15 axiomDBit (axiomDVal b.data) (by obj_loop ConLeche.Frontend.scanAxiomDeclLoop b) i w seen (a0, a1, a2, a3)

/-- con-leche's `scanAxiomDecl`. -/
@[refines_part ConLeche.Frontend.scanAxiomDecl "validity"]
theorem axiomD_link (i : USize) : okW (ConLeche.Frontend.scanAxiomDecl b i) = axiomDN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanAxiomDecl axiomDN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (axiomDLoop_link b h64 hsize (i + 1) true 0 false _ 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [axiomD_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanDefDeclLoop`. -/
theorem defDLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : HintsRec) (a1 : List Nat) (a2 : Nat) (a3 : String) (a4 : Nat) (a5 : Nat) :
    okW (ConLeche.Frontend.scanDefDeclLoop b i w seen a0 a1 a2 a3 a4 a5) =
      objN defDBit (defDVal b.data) 124 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : HintsRec × List Nat × Nat × String × Nat × Nat) => ConLeche.Frontend.scanDefDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2)
    124 defDBit (defDVal b.data) (by obj_loop ConLeche.Frontend.scanDefDeclLoop b) i w seen (a0, a1, a2, a3, a4, a5)

/-- con-leche's `scanDefDecl`. -/
@[refines_part ConLeche.Frontend.scanDefDecl "validity"]
theorem defD_link (i : USize) : okW (ConLeche.Frontend.scanDefDecl b i) = defDN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanDefDecl defDN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (defDLoop_link b h64 hsize (i + 1) true 0 _ _ 0 "" 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [defD_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanThmDeclLoop`. -/
theorem thmDLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : List Nat) (a1 : Nat) (a2 : Nat) (a3 : Nat) :
    okW (ConLeche.Frontend.scanThmDeclLoop b i w seen a0 a1 a2 a3) =
      objN thmDBit (thmDVal b.data) 30 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : List Nat × Nat × Nat × Nat) => ConLeche.Frontend.scanThmDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2)
    30 thmDBit (thmDVal b.data) (by obj_loop ConLeche.Frontend.scanThmDeclLoop b) i w seen (a0, a1, a2, a3)

/-- con-leche's `scanThmDecl`. -/
@[refines_part ConLeche.Frontend.scanThmDecl "validity"]
theorem thmD_link (i : USize) : okW (ConLeche.Frontend.scanThmDecl b i) = thmDN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanThmDecl thmDN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (thmDLoop_link b h64 hsize (i + 1) true 0 _ 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [thmD_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanOpaqueDeclLoop`. -/
theorem opaqueDLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : Bool) (a1 : List Nat) (a2 : Nat) (a3 : Nat) (a4 : Nat) :
    okW (ConLeche.Frontend.scanOpaqueDeclLoop b i w seen a0 a1 a2 a3 a4) =
      objN opaqueDBit (opaqueDVal b.data) 62 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : Bool × List Nat × Nat × Nat × Nat) => ConLeche.Frontend.scanOpaqueDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2)
    62 opaqueDBit (opaqueDVal b.data) (by obj_loop ConLeche.Frontend.scanOpaqueDeclLoop b) i w seen (a0, a1, a2, a3, a4)

/-- con-leche's `scanOpaqueDecl`. -/
@[refines_part ConLeche.Frontend.scanOpaqueDecl "validity"]
theorem opaqueD_link (i : USize) : okW (ConLeche.Frontend.scanOpaqueDecl b i) = opaqueDN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanOpaqueDecl opaqueDN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (opaqueDLoop_link b h64 hsize (i + 1) true 0 false _ 0 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [opaqueD_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanQuotDeclLoop`. -/
theorem quotDLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : String) (a1 : List Nat) (a2 : Nat) (a3 : Nat) :
    okW (ConLeche.Frontend.scanQuotDeclLoop b i w seen a0 a1 a2 a3) =
      objN quotDBit (quotDVal b.data) 15 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : String × List Nat × Nat × Nat) => ConLeche.Frontend.scanQuotDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2)
    15 quotDBit (quotDVal b.data) (by obj_loop ConLeche.Frontend.scanQuotDeclLoop b) i w seen (a0, a1, a2, a3)

/-- con-leche's `scanQuotDecl`. -/
@[refines_part ConLeche.Frontend.scanQuotDecl "validity"]
theorem quotD_link (i : USize) : okW (ConLeche.Frontend.scanQuotDecl b i) = quotDN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanQuotDecl quotDN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (quotDLoop_link b h64 hsize (i + 1) true 0 "" _ 0 0)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [quotD_link _ ‹_› ‹_›]) <;> rfl)

/-- con-leche's `scanIndDeclLoop`. -/
theorem indDLoop_link (i : USize) (w : Bool) (seen : UInt32) (a0 : List IndCtorRec) (a1 : List IndRecRec) (a2 : List IndTypeRec) :
    okW (ConLeche.Frontend.scanIndDeclLoop b i w seen a0 a1 a2) =
      objN indDBit (indDVal b.data) 26 b.data i.toUInt64 (bw w) seen.toUInt64 :=
  objN_link b h64 hsize (fun i w seen (st : List IndCtorRec × List IndRecRec × List IndTypeRec) => ConLeche.Frontend.scanIndDeclLoop b i w seen st.1 st.2.1 st.2.2)
    26 indDBit (indDVal b.data) (by obj_loop ConLeche.Frontend.scanIndDeclLoop b) i w seen (a0, a1, a2)

/-- con-leche's `scanIndDecl`. -/
@[refines_part ConLeche.Frontend.scanIndDecl "validity"]
theorem indD_link (i : USize) : okW (ConLeche.Frontend.scanIndDecl b i) = indDN b.data i.toUInt64 := by
  unfold ConLeche.Frontend.scanIndDecl indDN objEntryN
  rw [entry_link b h64 hsize i 123 123 (by decide) rfl (by decide)
    (indDLoop_link b h64 hsize (i + 1) true 0 _ _ _)]
  rw [succ_toUInt64 b h64 hsize]; rfl

macro_rules | `(tactic| link_val) => `(tactic| (rw [indD_link _ ‹_› ‹_›]) <;> rfl)

end records

end ConAgua.Scan.RecordsLink
