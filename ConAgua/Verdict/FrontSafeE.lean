import ConAgua.Verdict.FrontRunE

set_option linter.deprecated false

/-!
# The scanner's `safety` converse (lane `verdicts-b`, helper `f2`)

`DeclR` (Front/DeclIface.lean) states of a definition's `safety` word only `flag = 1 → s = "safe"`.
`apply_decl`'s error claim needs the converse on the flag `0` (`decl_kind` declines a definition
whose flag is `0`): a `safety` con-leche reads as `"safe"` does not get flag `0`. Flag `2` (a body
with a backslash) can be `"safe"` (`"safe"`): `decl_kind` aborts there with
`R_ESCAPED_STRING`, a class-`0` code, which claims nothing.
-/

namespace ConAgua.Front.FieldsLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Front.Fields

theorem eq_toUTF8_of_fromUTF8? {x : ByteArray} {s : String} (h : String.fromUTF8? x = some s) :
    x = s.toUTF8 := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

section kitS
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

/-- **`str_code`'s converse for `safety`**: a string con-leche reads as `"safe"` does not get the
code `0`. -/
theorem strCode_safe (v : USize) (e : USize)
    (h : ConLeche.Frontend.scanString b v = .ok "safe" e) :
    strCodeN b.data (v.toUInt64 + 1) (e.toUInt64 - 1) 54 ≠ 0 := by
  have hS := scanString_strOK b h64 hsize v _ e h
  unfold ConLeche.Frontend.scanString at h
  split at h; cases h; rename_i hq
  have hv : v < b.usize := by
    refine Classical.byContradiction fun hn => ?_
    have h0 : byteAt b v = 0 := by unfold byteAt; rw [dif_neg hn]
    rw [h0] at hq; exact hq (by decide)
  have hv1 : (v.toUInt64 + 1).toNat = (v + 1).toNat := by
    rw [← succ_toUInt64 b h64 hsize, USize.toNat_toUInt64]
  have hc := strClose_toNat_eq b h64 (by omega) (v + 1)
  dsimp only at h
  split at h; cases h; rename_i hz
  have hz' : strClose b (v + 1) ≠ 0 := by simpa using hz
  have hcn : L.Examples.strCloseN b.data (v + 1).toNat ≠ 0 := by
    rw [← hc]; intro h0; exact hz' (USize.toNat_inj.mp (by rw [h0]; rfl))
  have hlt := L.Examples.strCloseN_bounds b.data (v + 1).toNat hcn
  have hbs : b.data.size = b.size := rfl
  have he : e = strClose b (v + 1) + 1 := by
    split at h
    · split at h
      · exact (ScanRes.ok.inj h).2.symm
      · cases h
    · split at h
      · exact (ScanRes.ok.inj h).2.symm
      · cases h
  subst he
  have he1 : ((strClose b (v + 1) + 1).toUInt64 - 1).toNat = (strClose b (v + 1)).toNat := by
    rw [succ_toUInt64 b h64 hsize, UInt64.add_sub_cancel, USize.toNat_toUInt64]
  generalize hC : v.toUInt64 + 1 = C at hv1 hS ⊢
  generalize hD : (strClose b (v + 1) + 1).toUInt64 - 1 = Dw at he1 hS ⊢
  rw [hc] at he1
  have hU : UInt64.size = 2 ^ 64 := rfl
  unfold strCodeN
  split
  · rename_i hlt'
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by omega)] at hlt'
    omega
  split
  · simp
  rename_i hesc
  have hesc' := hasEscapeN_eq_zero b _ _ hesc
  rw [if_pos rfl]
  have hx := eq_toUTF8_of_fromUTF8? (hS (noEsc_of_hasEscapeN_decl b _ _ hesc'))
  have hl := congrArg (fun x : ByteArray => x.data.toList) hx
  simp only [show "safe".toUTF8.data.toList = [115, 97, 102, 101] by rfl] at hl
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_take, List.length_drop, Array.length_toList, List.length_cons,
    List.length_nil] at hlen
  rw [if_pos]
  · decide
  refine ⟨?_, ?_⟩
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; omega)]
    simp; omega
  · rw [ConAgua.Scan.matchLitN_eq_isPrefixOf _ _ _ _ _ _ (by simp [DLITS_length]) (by decide)]
    simp only [Nat.add_zero, Nat.sub_zero, List.drop_zero]
    rw [show List.take 4 DLITS = [115, 97, 102, 101] by rfl, ← hl]
    apply List.isPrefixOf_iff_prefix.mpr
    rw [show Dw.toNat - C.toNat = 4 by omega]
    exact List.take_prefix _ _

end kitS

open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Member (nextMemberN)

/-- **The `safety` converse**: a definition whose `safety` con-leche reads as `"safe"` does not
have flag `0` (flag `2`, an escaped spelling, is possible). -/
def DeclSafeR' (d : DeclRec) (f : DFld) : Prop :=
  ∀ cv v h s, d = .defn cv v h s → s = "safe" → f.flag ≠ 0

/-- `DefR` and the `safety` converse. -/
def DefR' (b : ByteArray) (seen : UInt32) (st : HintsRec × List Nat × Nat × String × Nat × Nat)
    (f : DFld) : Prop :=
  DefR b seen st f ∧ (st.2.2.2.1 = "safe" → f.flag ≠ 0)

section recordsS
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem def_loop' : DObjLoop b (fun i w seen (st : HintsRec × List Nat × Nat × String × Nat × Nat) =>
      scanDefDeclLoop b i w seen st.1 st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2.1 st.2.2.2.2.2) (DefR' b)
    (fun d f => DeclR b d { f with pl := 21 } ∧ DeclSafeR' d f) := by
  constructor
  · dloop_stop scanDefDeclLoop
  · dloop_ws scanDefDeclLoop
  · dloop_close scanDefDeclLoop
    obtain ⟨⟨hh, hl, hn, hs, ht, hvl⟩, hs'⟩ := hR
    refine ⟨⟨rfl, ⟨hn, lpsR_close b _ _ _ _ _ hl hM (by decide) (by decide), ht⟩, hvl, hh, hs⟩, ?_⟩
    intro cv v hd s hd' hss
    cases hd'
    exact hs' hss
  · dloop_comma scanDefDeclLoop
  · dloop_quote scanDefDeclLoop
  · dloop_key scanDefDeclLoop
    all_goals obtain ⟨⟨hh, hl, hn, hs, ht, hvl⟩, hs'⟩ := hR
    case kName =>
      rw [show UInt64.ofNat Key.kName.ctorIdx = (34 : Word) from rfl]
      dkey_num (st.1, st.2.1, readNatAt b v (numEnd b v), st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2)
      exact ⟨⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hRn, hs, ht, hvl⟩, hs'⟩
    case kType =>
      rw [show UInt64.ofNat Key.kType.ctorIdx = (61 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, st.2.2.2.1, readNatAt b v (numEnd b v), st.2.2.2.2.2)
      exact ⟨⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, hRn, hvl⟩, hs'⟩
    case kValue =>
      rw [show UInt64.ofNat Key.kValue.ctorIdx = (65 : Word) from rfl]
      dkey_num (st.1, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, readNatAt b v (numEnd b v))
      exact ⟨⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, ht, hRn⟩, hs'⟩
    case kLevelParams =>
      rw [show UInt64.ofNat Key.kLevelParams.ctorIdx = (31 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, (st.1, x, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2),
        by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte]
      exact ⟨⟨hh, .inl (list_link b h64 hsize v x e' hx), hn, hs, ht, hvl⟩, hs'⟩
    case kAll =>
      rw [show UInt64.ofNat Key.kAll.ctorIdx = (1 : Word) from rfl]
      dkey_res
      have hend := scanNatList_link b h64 hsize v
      rw [hx] at hend
      refine ⟨e', _, st, by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte]
      exact ⟨⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, ht, hvl⟩, hs'⟩
    case kHints =>
      rw [show UInt64.ofNat Key.kHints.ctorIdx = (15 : Word) from rfl]
      dkey_res
      have hend := scanHints_link b h64 hsize v
      rw [hx] at hend
      have hH := hkv_link b h64 hsize v x e' hx
      refine ⟨e', _, (x, st.2.1, st.2.2.1, st.2.2.2.1, st.2.2.2.2.1, st.2.2.2.2.2),
        by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte]
      exact ⟨⟨hH, lpsR_or b _ _ _ _ _ hl (by decide), hn, hs, ht, hvl⟩, hs'⟩
    case kSafety =>
      rw [show UInt64.ofNat Key.kSafety.ctorIdx = (54 : Word) from rfl]
      dkey_res
      have hend := scanString_link b h64 hsize v
      rw [hx] at hend
      have hq := (strCode_link b h64 hsize v x e' hx 54).1 rfl
      refine ⟨e', _, (st.1, st.2.1, st.2.2.1, x, st.2.2.2.2.1, st.2.2.2.2.2),
        by simp [dstepN, dendN, ← hend, okW], hie, hok, ?_⟩
      simp (config := {decide := true}) only [dstepN, dnumN, dlpsN, dflagN, dhkN, dhnN, ↓reduceIte,
        ← hend, okW]
      refine ⟨⟨hh, lpsR_or b _ _ _ _ _ hl (by decide), hn, hq, ht, hvl⟩, ?_⟩
      intro hxs
      subst hxs
      exact strCode_safe b h64 hsize v e' hx
  · dloop_other scanDefDeclLoop

end recordsS
end ConAgua.Front.FieldsLink
#print axioms ConAgua.Front.FieldsLink.def_loop'
#print axioms ConAgua.Front.FieldsLink.strCode_safe
