import ConAgua.Arena.RomLevels
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The decoder direction of the ROM readers' models (lane `romload`)

The pin data is untrusted (DESIGN.md, "The pin data as an input"), so the readers' models must
also say: **a model that returns read an encoding**. For any `rom` with `RomOK rom`:

* `romNameW_dec`: `romNameW rom n m pos = some (h, q, m')` ⇒ the bytes at `pos` are
  `encName x ++ rest` for a fitting name `x`, and `q` is the position after it;
* `romLevelW_dec`, `romLvlsW_dec`, `romLevelsW_dec`: the same for a level, `k` levels, a
  universe-argument list (`< 2^60` levels: `rom_levels` checks the count).

The models read `255` past the ROM's end (no tag), and record `rom_u64`'s range check (`u64OK`),
so every byte a returning model consumed is in the ROM. A `str` name's bytes passed `rom_put`'s
ASCII check, so they are the UTF-8 of `asciiStr bytes` (`asciiStr_bytes`).
-/

open Std.WP

namespace L.Rom

open L.Arena

/-! ## ASCII bytes are a string's UTF-8 -/

/-- The string whose characters are the bytes. -/
def asciiStr (bs : List UInt8) : String := String.ofList (bs.map fun b => Char.ofNat b.toNat)

theorem char_ofNat_ascii (b : UInt8) (hb : b.toNat < 128) : (Char.ofNat b.toNat).val.toNat = b.toNat := by
  rw [Char.ofNat, dite_eq_left (by left; omega)]
  simp [Char.ofNatAux]

theorem utf8Encode_ascii (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) :
    (bs.map fun b => Char.ofNat b.toNat).utf8Encode.data.toList = bs := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    have hb := h b (by simp)
    have hc := char_ofNat_ascii b hb
    rw [List.map_cons, List.utf8Encode_cons, List.utf8Encode_singleton,
      String.utf8EncodeChar_eq_singleton]
    · simp [ih (fun x hx => h x (by simp [hx]))]
      apply UInt8.toNat_inj.mp
      show (Char.ofNat b.toNat).val.toUInt8.toNat = _
      simp only [UInt32.toNat_toUInt8, hc]; omega
    · rw [Char.utf8Size_eq_one_iff, UInt32.le_iff_toNat_le, hc]; simp; omega

/-- **ASCII bytes are the UTF-8 of `asciiStr`.** -/
theorem asciiStr_bytes (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) :
    (asciiStr bs).toByteArray.data.toList = bs := by
  rw [asciiStr, String.toByteArray_ofList]; exact utf8Encode_ascii bs h

theorem asciiStr_size (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) :
    (asciiStr bs).toByteArray.size = bs.length := by
  have := congrArg List.length (asciiStr_bytes bs h)
  simpa using this

section rom
variable (rom : List UInt8) (hr : RomOK rom)

/-! ## Bytes the models read -/

/-- A tag below `255` read at `pos`: the byte is there. -/
theorem romB_tag (pos : Word) (c : Nat) (hc : c < 255) (h : romB rom pos = UInt64.ofNat c) :
    pos.toNat < rom.length ∧ rom.drop pos.toNat = UInt8.ofNat c :: rom.drop (pos.toNat + 1) := by
  simp only [romB] at h
  by_cases hp : pos.toNat < rom.length
  · rw [List.getElem?_eq_getElem hp, Option.getD_some] at h
    have hb : rom[pos.toNat] = UInt8.ofNat c := by
      apply UInt8.toNat_inj.mp
      have := congrArg UInt64.toNat h
      simp only [UInt8.toNat_toUInt64, UInt64.toNat_ofNat'] at this
      simp [this]; omega
    refine ⟨hp, ?_⟩
    rw [List.drop_eq_getElem_cons hp, hb]
  · rw [List.getElem?_eq_none (by omega), Option.getD_none] at h
    have := congrArg UInt64.toNat h
    simp [UInt64.toNat_ofNat'] at this; omega

include hr in
theorem pos_succ (pos : Word) (hp : pos.toNat < rom.length) : (pos + 1).toNat = pos.toNat + 1 := by
  simp only [RomOK] at hr
  rw [UInt64.toNat_add]; simp; omega

theorem u64B_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    u64B (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 + b4.toNat * 4294967296 +
      b5.toNat * 1099511627776 + b6.toNat * 281474976710656 + b7.toNat * 72057594037927936) =
      [b0, b1, b2, b3, b4, b5, b6, b7] := by
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
  simp only [u64B, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> apply UInt8.toNat_inj.mp <;> simp <;> omega

include hr in
/-- **A number read by a returning model is there**: `u64OK` gives its eight bytes. -/
theorem u64_dec (q : Word) (hu : u64OK rom q) :
    q.toNat + 8 ≤ rom.length ∧ (q + 8).toNat = q.toNat + 8 ∧
      rom.drop q.toNat = u64B (u64W rom q).toNat ++ rom.drop (q.toNat + 8) := by
  simp only [RomOK] at hr
  obtain ⟨h1, h2⟩ := hu
  have hq8 : (q + 8).toNat = q.toNat + 8 := by
    have := UInt64.le_iff_toNat_le.mp h2
    have e := UInt64.toNat_add q 8
    have := q.toNat_lt
    simp only [UInt64.reduceToNat] at e this ⊢
    omega
  have hl : q.toNat + 8 ≤ rom.length := by
    have := UInt64.le_iff_toNat_le.mp h1
    rw [hq8, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega)] at this
    exact this
  refine ⟨hl, hq8, ?_⟩
  have hbs : rom.drop q.toNat = (rom.drop q.toNat).take 8 ++ rom.drop (q.toNat + 8) := by
    conv => lhs; rw [← List.take_append_drop 8 (rom.drop q.toNat)]
    rw [List.drop_drop]
  have hlen : ((rom.drop q.toNat).take 8).length = 8 := by simp; omega
  generalize (rom.drop q.toNat).take 8 = bs at hbs hlen
  match bs, hlen with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    rw [hbs]
    congr 1
    have hq : ∀ k : Nat, k < 8 → (q + UInt64.ofNat k).toNat = q.toNat + k := fun k hk => by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega
    have b := fun k hk q' hq' => romB_of_drop rom q [b0, b1, b2, b3, b4, b5, b6, b7] _ hbs k hk q' hq'
    have e0 := b 0 (by simp) q (by simp)
    have e1 := b 1 (by simp) (q + 1) (hq 1 (by omega))
    have e2 := b 2 (by simp) (q + 2) (hq 2 (by omega))
    have e3 := b 3 (by simp) (q + 3) (hq 3 (by omega))
    have e4 := b 4 (by simp) (q + 4) (hq 4 (by omega))
    have e5 := b 5 (by simp) (q + 5) (hq 5 (by omega))
    have e6 := b 6 (by simp) (q + 6) (hq 6 (by omega))
    have e7 := b 7 (by simp) (q + 7) (hq 7 (by omega))
    have hN : (u64W rom q).toNat = b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
        b4.toNat * 4294967296 + b5.toNat * 1099511627776 + b6.toNat * 281474976710656 +
        b7.toNat * 72057594037927936 := by
      simp only [u64W, e0, e1, e2, e3, e4, e5, e6, e7]
      have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
      have := b4.toNat_lt; have := b5.toNat_lt; have := b6.toNat_lt; have := b7.toNat_lt
      simp only [List.getElem_cons_zero, List.getElem_cons_succ, UInt8.toUInt64, UInt64.toNat_add,
        UInt64.toNat_mul]
      simp
      omega
    rw [hN, u64B_bytes]

/-- `asciiW` from `j` on: every byte below `128`. -/
theorem asciiW_get (i l : Word) :
    ∀ (e : Nat) (j : Word), l.toNat - j.toNat = e → asciiW rom i l j = true →
      ∀ k, j.toNat ≤ k → k < l.toNat → romB rom (i + UInt64.ofNat k) < 128 := by
  intro e
  induction e with
  | zero => intro j he _ k hk hk'; omega
  | succ e ih =>
    intro j he hW k hk hk'
    have hj : j < l := by rw [UInt64.lt_iff_toNat_lt]; omega
    have := l.toNat_lt
    have hj1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    rw [asciiW] at hW
    simp only [hj, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq] at hW
    by_cases hk0 : k = j.toNat
    · subst hk0; simpa using hW.1
    · exact ih (j + 1) (by omega) hW.2 k (by omega) hk'

include hr in
/-- **`rom_put`'s checks give the bytes**: in the ROM, and ASCII. -/
theorem romPutOK_bytes (m : Mem) (i l : Word) (h : romPutOK rom m i l) :
    i.toNat + l.toNat ≤ rom.length ∧ ∀ b ∈ (rom.drop i.toNat).take l.toNat, b.toNat < 128 := by
  simp only [RomOK] at hr
  obtain ⟨h1, h2, -, -, h5⟩ := h
  have hil : (i + l).toNat = i.toNat + l.toNat := by
    have := UInt64.le_iff_toNat_le.mp h2
    have := i.toNat_lt; have := l.toNat_lt
    have e := UInt64.toNat_add i l
    rw [show (2:Nat)^64 = 18446744073709551616 from rfl] at *
    omega
  have hin : i.toNat + l.toNat ≤ rom.length := by
    have := UInt64.le_iff_toNat_le.mp h1
    rw [hil, UInt64.toNat_ofNat'] at this
    rwa [Nat.mod_eq_of_lt (by omega)] at this
  refine ⟨hin, fun b hb => ?_⟩
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hb
  simp only [List.length_take, List.length_drop] at hk
  have ha := asciiW_get rom i l _ 0 rfl h5 k (by simp) (by omega)
  have hik : (i + UInt64.ofNat k).toNat = i.toNat + k := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat']; simp; omega
  rw [romB_eq rom _ (i.toNat + k) hik.symm (by omega)] at ha
  simp only [List.getElem_take, List.getElem_drop]
  have := UInt64.lt_iff_toNat_lt.mp ha
  simpa using this

/-! ## Names -/

theorem nmAnonK_inv {pos h q : Word} {m' : Mem} {x : Option (Word × Mem)}
    (hW : nmAnonK pos x = some (h, q, m')) : q = pos + 1 := by
  match x, hW with
  | some (w, m₁), hW =>
    simp only [nmAnonK] at hW
    split at hW
    · simp at hW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hW; exact hW.2.1.symm

theorem nmNumK_inv {q₁ h q : Word} {m' : Mem} {x : Option (Word × Mem)}
    (hW : nmNumK q₁ x = some (h, q, m')) : q = q₁ + 8 := by
  match x, hW with
  | some (w, m₁), hW =>
    simp only [nmNumK] at hW
    split at hW
    · simp at hW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hW; exact hW.2.1.symm

theorem nmStrK_inv {h₁ q₁ l h q : Word} {m' : Mem} {x : Option (Word × Mem)}
    (hW : nmStrK h₁ q₁ l x = some (h, q, m')) : q = q₁ + 8 + l := by
  match x, hW with
  | some (o, m₂), hW =>
    simp only [nmStrK] at hW
    rcases hI : nsinternW m₂ h₁ o l with _ | ⟨w, m₃⟩ <;> rw [hI] at hW
    · simp [nmStr2K] at hW
    simp only [nmStr2K] at hW
    split at hW
    · simp at hW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hW; exact hW.2.1.symm

include hr in
/-- **The decoder direction of `rom_name`'s model**: it returned, so the bytes at `pos` are the
encoding of a fitting name, and `q` is the position after it. -/
theorem romNameW_dec : ∀ (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem),
    romNameW rom n m pos = some (h, q, m') →
    ∃ x rest, rom.drop pos.toNat = encName x ++ rest ∧ nameFits x = true ∧
      q.toNat = pos.toNat + (encName x).length := by
  intro n
  induction n with
  | zero => intro m pos h q m' hW; simp [romNameW] at hW
  | succ n ih =>
    intro m pos h q m' hW
    have hr' := hr
    simp only [RomOK] at hr'
    by_cases h0 : romB rom pos = 0
    · rw [romNameW_anon rom n m pos h0] at hW
      obtain ⟨hp, hd⟩ := romB_tag rom pos 0 (by omega) h0
      refine ⟨.anonymous, rom.drop (pos.toNat + 1), by simpa [encName] using hd, rfl, ?_⟩
      rw [nmAnonK_inv hW, pos_succ rom hr pos hp]; simp [encName]
    rw [romNameW_rec rom n m pos h0] at hW
    rcases hP : romNameW rom n m (pos + 1) with _ | ⟨h₁, q₁, m₁⟩ <;> rw [hP] at hW
    · simp [nmRecK] at hW
    obtain ⟨pre, rest₁, hd1, hf1, hq1⟩ := ih m (pos + 1) h₁ q₁ m₁ hP
    simp only [nmRecK] at hW
    by_cases hu : u64OK rom q₁
    case neg => simp [hu] at hW
    simp only [hu, not_true_eq_false, ↓reduceIte] at hW
    obtain ⟨hl8, hq8, hdq⟩ := u64_dec rom hr q₁ hu
    by_cases h1 : romB rom pos = 1
    · rw [ite_eq_left h1] at hW
      obtain ⟨hp, hd⟩ := romB_tag rom pos 1 (by omega) h1
      have hp1 := pos_succ rom hr pos hp
      have hrest1 : rest₁ = rom.drop q₁.toNat := by
        rw [hq1, hp1, ← List.drop_drop, ← hp1, hd1, List.drop_left]
      simp only [romPutW] at hW
      by_cases hok : romPutOK rom m₁ (q₁ + 8) (u64W rom q₁)
      case neg => rw [ite_eq_right hok] at hW; simp [nmStrK] at hW
      rw [ite_eq_left hok] at hW
      have hq := nmStrK_inv hW
      obtain ⟨hin, hasc⟩ := romPutOK_bytes rom hr m₁ _ _ hok
      rw [hq8] at hin hasc
      generalize u64W rom q₁ = l at hW hok hq hin hasc hdq
      obtain ⟨bs, hbs⟩ : ∃ bs, bs = (rom.drop (q₁.toNat + 8)).take l.toNat := ⟨_, rfl⟩
      rw [← hbs] at hasc
      have hbl : bs.length = l.toNat := by rw [hbs]; simp; omega
      have hsz := asciiStr_size bs hasc
      have hdat := asciiStr_bytes bs hasc
      have hdq' : rom.drop q₁.toNat = strB (asciiStr bs) ++ rom.drop (q₁.toNat + 8 + l.toNat) := by
        rw [hdq, strB, hsz, hbl, hdat, List.append_assoc, hbs, ← List.drop_drop (i := l.toNat),
          List.take_append_drop]
      refine ⟨.str pre (asciiStr bs), rom.drop (q₁.toNat + 8 + l.toNat), ?_, ?_, ?_⟩
      · rw [hd, encName, ← hp1, hd1, hrest1, hdq']; simp
      · simp only [nameFits, hf1, Bool.true_and, decide_eq_true_eq, hsz, hbl]; omega
      · rw [hq, UInt64.toNat_add, hq8]
        simp only [encName, strB, List.length_cons, List.length_append, hsz, hbl, u64B,
          List.length_nil]
        rw [hdat, hbl, hq1, hp1]; simp; omega
    · rw [ite_eq_right h1] at hW
      by_cases h2 : romB rom pos = 2
      case neg => rw [ite_eq_right h2] at hW; simp at hW
      rw [ite_eq_left h2] at hW
      obtain ⟨hp, hd⟩ := romB_tag rom pos 2 (by omega) h2
      have hp1 := pos_succ rom hr pos hp
      have hrest1 : rest₁ = rom.drop q₁.toNat := by
        rw [hq1, hp1, ← List.drop_drop, ← hp1, hd1, List.drop_left]
      have hq := nmNumK_inv hW
      refine ⟨.num pre (u64W rom q₁).toNat, rom.drop (q₁.toNat + 8), ?_, ?_, ?_⟩
      · rw [hd, encName, ← hp1, hd1, hrest1, hdq]; simp
      · simp [nameFits, hf1, (u64W rom q₁).toNat_lt]
      · rw [hq, hq8, hq1, hp1]; simp [encName, u64B]; omega

/-! ## Levels -/

theorem lvNodeK_inv {q h q' : Word} {m' : Mem} {x : Option (Word × Mem)}
    (hW : lvNodeK q x = some (h, q', m')) : q' = q := by
  match x, hW with
  | some (w, m₁), hW =>
    simp only [lvNodeK] at hW
    split at hW
    · simp at hW
    · simp only [Option.some.injEq, Prod.mk.injEq] at hW; exact hW.2.1.symm

include hr in
/-- **The decoder direction of `rom_level`'s model.** -/
theorem romLevelW_dec : ∀ (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem),
    romLevelW rom n m pos = some (h, q, m') →
    ∃ u rest, rom.drop pos.toNat = encLevel u ++ rest ∧ levelFits u = true ∧
      q.toNat = pos.toNat + (encLevel u).length := by
  intro n
  induction n with
  | zero => intro m pos h q m' hW; simp [romLevelW] at hW
  | succ n ih =>
    intro m pos h q m' hW
    have hr' := hr
    simp only [RomOK] at hr'
    by_cases h0 : romB rom pos = 0
    · rw [romLevelW_zero rom n m pos h0] at hW
      obtain ⟨hp, hd⟩ := romB_tag rom pos 0 (by omega) h0
      refine ⟨.zero, rom.drop (pos.toNat + 1), by simpa [encLevel] using hd, rfl, ?_⟩
      rw [lvNodeK_inv hW, pos_succ rom hr pos hp]; simp [encLevel]
    by_cases h4 : romB rom pos = 4
    · rw [romLevelW_param rom n m pos h0 h4] at hW
      obtain ⟨hp, hd⟩ := romB_tag rom pos 4 (by omega) h4
      have hp1 := pos_succ rom hr pos hp
      rcases hP : romNameW rom n m (pos + 1) with _ | ⟨u, q₁, m₁⟩ <;> rw [hP] at hW
      · simp [lvParamK] at hW
      rw [lvParamK_some] at hW
      obtain ⟨x, rest₁, hd1, hf1, hq1⟩ := romNameW_dec rom hr n m (pos + 1) u q₁ m₁ hP
      refine ⟨.param x, rest₁, ?_, hf1, ?_⟩
      · rw [hd, encLevel, ← hp1, hd1]; simp
      · rw [lvNodeK_inv hW, hq1, hp1]; simp [encLevel]; omega
    rw [romLevelW_rec rom n m pos h0 h4] at hW
    rcases hU : romLevelW rom n m (pos + 1) with _ | ⟨hu, q₁, m₁⟩ <;> rw [hU] at hW
    · simp [lvOneK] at hW
    obtain ⟨u, rest₁, hd1, hf1, hq1⟩ := ih m (pos + 1) hu q₁ m₁ hU
    by_cases h1 : romB rom pos = 1
    · rw [lvOneK_succ rom n _ _ _ _ h1] at hW
      obtain ⟨hp, hd⟩ := romB_tag rom pos 1 (by omega) h1
      have hp1 := pos_succ rom hr pos hp
      refine ⟨.succ u, rest₁, ?_, hf1, ?_⟩
      · rw [hd, encLevel, ← hp1, hd1]; simp
      · rw [lvNodeK_inv hW, hq1, hp1]; simp [encLevel]; omega
    rw [lvOneK_two rom n _ _ _ _ h1] at hW
    rcases hV : romLevelW rom n m₁ q₁ with _ | ⟨hv, q₂, m₂⟩ <;> rw [hV] at hW
    · simp [lvTwoK] at hW
    obtain ⟨v, rest₂, hd2, hf2, hq2⟩ := ih m₁ q₁ hv q₂ m₂ hV
    have hrest : ∀ (pos' : Word) (c : Nat), romB rom pos = UInt64.ofNat c → c < 255 →
        rom.drop pos.toNat = UInt8.ofNat c :: (encLevel u ++ encLevel v ++ rest₂) := by
      intro _ c hc hc'
      obtain ⟨hp, hd⟩ := romB_tag rom pos c hc' hc
      have hp1 := pos_succ rom hr pos hp
      have hrest1 : rest₁ = rom.drop q₁.toNat := by
        rw [hq1, hp1, ← List.drop_drop, ← hp1, hd1, List.drop_left]
      rw [hd, ← hp1, hd1, hrest1, hd2, List.append_assoc]
    have hp : pos.toNat < rom.length := by
      by_cases h2 : romB rom pos = 2
      · exact (romB_tag rom pos 2 (by omega) h2).1
      by_cases h3 : romB rom pos = 3
      · exact (romB_tag rom pos 3 (by omega) h3).1
      simp [lvTwoK, h2, h3] at hW
    have hp1 := pos_succ rom hr pos hp
    have hlen : q.toNat = pos.toNat + 1 + (encLevel u).length + (encLevel v).length := by
      have : q = q₂ := by
        simp only [lvTwoK] at hW
        split at hW
        · exact lvNodeK_inv hW
        split at hW
        · exact lvNodeK_inv hW
        · simp at hW
      rw [this, hq2, hq1, hp1]
    by_cases h2 : romB rom pos = 2
    · refine ⟨.max u v, rest₂, ?_, by simp [levelFits, hf1, hf2], ?_⟩
      · rw [hrest pos 2 h2 (by omega), encLevel]; simp
      · rw [hlen]; simp [encLevel]; omega
    by_cases h3 : romB rom pos = 3
    · refine ⟨.imax u v, rest₂, ?_, by simp [levelFits, hf1, hf2], ?_⟩
      · rw [hrest pos 3 h3 (by omega), encLevel]; simp
      · rw [hlen]; simp [encLevel]; omega
    simp [lvTwoK, h2, h3] at hW

/-! ## Level lists -/

include hr in
/-- **The decoder direction of `rom_lvls_go`'s model**: `k` levels. -/
theorem romLvlsW_dec : ∀ (n : Nat) (m : Mem) (q k r : Word) (m' : Mem),
    romLvlsW rom n m q k = some (r, m') →
    ∃ us rest, rom.drop q.toNat = encLevelList us ++ rest ∧ us.all levelFits = true ∧
      us.length = k.toNat ∧ r.toNat = q.toNat + (encLevelList us).length := by
  intro n
  induction n with
  | zero => intro m q k r m' hW; simp [romLvlsW] at hW
  | succ n ih =>
    intro m q k r m' hW
    by_cases hk : k = 0
    · subst hk
      rw [romLvlsW_zero] at hW
      simp only [Option.some.injEq, Prod.mk.injEq] at hW
      obtain ⟨hq, -⟩ := hW
      subst hq
      exact ⟨[], rom.drop q.toNat, by simp [encLevelList], rfl, by simp, by simp [encLevelList]⟩
    rw [romLvlsW_succ rom n m q k hk] at hW
    rcases hN : romLevelW rom n m q with _ | ⟨h₁, q₁, m₁⟩ <;> rw [hN] at hW
    · simp [lvlsK] at hW
    simp only [lvlsK] at hW
    split at hW
    case isFalse => simp at hW
    obtain ⟨u, rest₁, hd1, hf1, hq1⟩ := romLevelW_dec rom hr n m q h₁ q₁ m₁ hN
    obtain ⟨us, rest₂, hd2, hf2, hl2, hr2⟩ := ih _ q₁ (k - 1) r m' hW
    have hk1 : (k - 1).toNat = k.toNat - 1 := by
      have : 1 ≤ k.toNat := by
        rcases Nat.eq_zero_or_pos k.toNat with h | h
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hk
        · exact h
      rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simpa using this))]; simp
    have hrest1 : rest₁ = rom.drop q₁.toNat := by
      rw [hq1, ← List.drop_drop, hd1, List.drop_left]
    refine ⟨u :: us, rest₂, ?_, by simp [hf1, hf2], ?_, ?_⟩
    · rw [hd1, hrest1, hd2, encLevelList, List.append_assoc]
    · have : 1 ≤ k.toNat := by
        rcases Nat.eq_zero_or_pos k.toNat with h | h
        · exact absurd (UInt64.toNat_inj.mp (by simpa using h)) hk
        · exact h
      simp; omega
    · rw [hr2, hq1]; simp [encLevelList]; omega

include hr in
/-- **The decoder direction of `rom_levels`'s model**: a universe-argument list, shorter than
`2^60`. -/
theorem romLevelsW_dec (n : Nat) (m : Mem) (pos h q : Word) (m' : Mem)
    (hW : romLevelsW rom n m pos = some (h, q, m')) :
    ∃ us rest, rom.drop pos.toNat = encLevels us ++ rest ∧ us.all levelFits = true ∧
      us.length < 2 ^ 60 ∧ q.toNat = pos.toNat + (encLevels us).length := by
  cases n with
  | zero => simp [romLevelsW] at hW
  | succ n =>
  by_cases hu : u64OK rom pos
  case neg => simp [romLevelsW, hu] at hW
  by_cases hk : 1152921504606846976 ≤ u64W rom pos
  · simp [romLevelsW, hu, hk] at hW
  rw [romLevelsW_eq rom n m pos hu hk] at hW
  obtain ⟨hl8, hp8, hd0⟩ := u64_dec rom hr pos hu
  rcases hG : romLvlsW rom n m (pos + 8) (u64W rom pos) with _ | ⟨q₁, m₁⟩ <;> rw [hG] at hW
  · simp [lvsK] at hW
  have hq : q = q₁ := by
    simp only [lvsK] at hW
    split at hW
    case isFalse => simp at hW
    cases hI : lsinternW (((sputW m₁ (m₁.top >>> 40) (m₁.top &&& 1099511627775) (stkTop m) (u64W rom pos) 0).set64 CTL 0
        (m₁.top + u64W rom pos)).set64 CTL 131 (stkTop m)) m₁.top (u64W rom pos) with
    | none => rw [hI] at hW; simp [lsK] at hW
    | some r =>
      obtain ⟨w, m₂⟩ := r
      rw [hI] at hW
      simp only [lsK] at hW
      split at hW
      · simp at hW
      · simp only [Option.some.injEq, Prod.mk.injEq] at hW; exact hW.2.1.symm
  obtain ⟨us, rest, hd1, hf1, hl1, hq1⟩ := romLvlsW_dec rom hr n m (pos + 8) _ q₁ m₁ hG
  have hk' : us.length < 2 ^ 60 := by
    rw [hl1]
    have : ¬ (1152921504606846976 ≤ (u64W rom pos).toNat) := fun h =>
      hk (UInt64.le_iff_toNat_le.mpr (by simpa using h))
    omega
  refine ⟨us, rest, ?_, hf1, hk', ?_⟩
  · rw [hd0, encLevels, ← hl1, List.append_assoc, ← hp8, hd1]
  · rw [hq, hq1, hp8]; simp [encLevels, u64B]; omega

end rom

end L.Rom
