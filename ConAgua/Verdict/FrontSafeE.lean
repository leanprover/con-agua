import ConAgua.Verdict.FrontRunE


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
    have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right hn]
    rw [h0] at hq; exact hq (by decide)
  have hv1 : (v.toUInt64 + 1).toNat = (v + 1).toNat := by
    rw [← succ_toUInt64 h64, USize.toNat_toUInt64]
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
    rw [succ_toUInt64 h64, UInt64.add_sub_cancel, USize.toNat_toUInt64]
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
  rw [ite_eq_left rfl]
  have hx := eq_toUTF8_of_fromUTF8? (hS (noEsc_of_hasEscapeN_decl b _ _ hesc'))
  have hl := congrArg (fun x : ByteArray => x.data.toList) hx
  simp only [show "safe".toUTF8.data.toList = [115, 97, 102, 101] by rfl] at hl
  rw [ByteArray.data_extract, Array.toList_extract, List.extract_eq_take_drop] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_take, List.length_drop, Array.length_toList, List.length_cons,
    List.length_nil] at hlen
  rw [ite_eq_left]
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

theorem defEntry_link' (v : USize) (d : DeclRec) (e : USize) (h : scanDefDecl b v = .ok d e) :
    (dobjEntryN b.data v.toUInt64).pl = e.toUInt64 ∧
      DeclR b d { dobjEntryN b.data v.toUInt64 with pl := 21 } ∧
      DeclSafeR' d { dobjEntryN b.data v.toUInt64 with pl := 21 } := by
  unfold scanDefDecl at h
  split at h
  · rename_i hc
    unfold dobjEntryN; rw [← (obj_open b h64 hsize v hc).2]
    obtain ⟨h1, h2, h3⟩ := dobj_link b h64 hsize _ _ _ (def_loop' b h64 hsize) (v + 1) true 0
      (.regular 0, [], 0, "", 0, 0) DFld.init d e h
      ⟨⟨⟨rfl, itemR_zero⟩, .inr rfl, itemR_zero, fun h => absurd h (by decide), itemR_zero, itemR_zero⟩,
        fun h => absurd h (by decide)⟩
    exact ⟨h1, h2, h3⟩
  · cases h

omit h64 hsize in
theorem declSafe_of_pl {d : DeclRec} {f : DFld} (hD : DeclR b d f) (hpl : f.pl ≠ 21) :
    DeclSafeR' d f := by
  intro cv v h s hd
  subst hd
  exact absurd hD.1 hpl

theorem declLine_link' (i : USize) (w : Bool) (ik : UInt8) (idx : Nat) (pl : LinePayload) (f : DFld)
    (r : LineRec) (e : USize) (h : scanLineLoop b i w ik idx pl = .ok r e)
    (hP : DPlR b pl f ∧ ∀ d, pl = .decl d → DeclSafeR' d f) :
    (declN b.data i.toUInt64 (bw w) f).pl ≠ 0 →
      ∀ d, r = .decl d → DeclSafeR' d (declN b.data i.toUInt64 (bw w) f) := by
  rw [scanLineLoop.eq_def] at h
  by_cases hi : i < b.usize
  · have hin := usizeInBounds b i hi
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i hi
    rw [dite_eq_left hi] at h
    simp only [uget_byteAt _ i hi] at h
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true] at h
      rw [declN_congr _ _ _ _ _ _ (nm_ws b h64 hsize i _ hi hws)]
      exact declLine_link' (i + 1) w ik idx pl f r e h hP
    simp only [hws, Bool.false_eq_true, ite_false] at h
    by_cases h125 : byteAt b i = 125
    · simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true] at h
      rw [declN_close _ _ _ _ (by rw [nm_close b h64 hsize i _ hi hws h125])]
      split at h; cases h
      cases pl
      · simp at h
      · exact hP.1.elim
      · exact hP.1.elim
      · exact hP.1.elim
      · by_cases hk : ik = 0
        · subst hk; obtain ⟨rfl, rfl⟩ := ScanRes.ok.inj h
          exact fun _ d hd => by cases hd; exact hP.2 _ rfl
        · simp [hk] at h
      · exact hP.1.elim
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true,
      ite_false] at h
    by_cases h44 : byteAt b i = 44
    · simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true] at h
      split at h; cases h; rename_i hw
      have hw' : w = false := by simpa using hw
      subst hw'
      simp only [bw, Bool.false_eq_true, ite_false]
      rw [declN_congr _ _ _ _ _ _ (nm_comma b h64 hsize i hi hws h44)]
      exact declLine_link' (i + 1) true ik idx pl f r e h hP
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
      rw [declN_key _ _ _ _ (by rw [hm]; exact (by decide : (2 : Word) ≠ 0))
        (by rw [hm]; exact (by decide : (2 : Word) ≠ 1))]
      simp only [hm]
      generalize valueAt b i (keyEnd b (i + 1)) = v at h
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K at h
      cases K
      all_goals (try dsimp only at h)
      all_goals (try (cases h; done))
      all_goals simp (config := {decide := true}) only [dlvN, dendDN, dplN, dpickN, dnameN, declCode, ↓reduceIte, UInt64.not_lt_zero]
      all_goals (try exact fun h0 => absurd rfl h0)
      all_goals (try exact fun h0 => h0.elim)
      case kAxiom =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := axEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link' e' false ik idx (.decl d') _ r e h
            ⟨hD, fun d hd => by cases hd; exact declSafe_of_pl b hD (by simp)⟩
        · cases h
      case kDef =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD, hS⟩ := defEntry_link' b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link' e' false ik idx (.decl d') _ r e h ⟨hD, fun d hd => by cases hd; exact hS⟩
        · cases h
      case kThm =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := thmEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link' e' false ik idx (.decl d') _ r e h
            ⟨hD, fun d hd => by cases hd; exact declSafe_of_pl b hD (by simp)⟩
        · cases h
      case kOpaque =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := opaqueEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link' e' false ik idx (.decl d') _ r e h
            ⟨hD, fun d hd => by cases hd; exact declSafe_of_pl b hD (by simp)⟩
        · cases h
      case kQuot =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          obtain ⟨hpl, hD⟩ := quotEntry_link b h64 hsize v d' e' hd
          rw [hpl, ite_eq_left ((lt_toUInt64_iff _ _).mp hie)]
          exact declLine_link' e' false ik idx (.decl d') _ r e h
            ⟨hD, fun d hd => by cases hd; exact declSafe_of_pl b hD (by simp)⟩
        · cases h
      case kInductive =>
        split at h; cases h
        split at h; cases h; rename_i d' e' hd
        split at h
        · rename_i hie
          have hpl := indD_link b h64 hsize v
          rw [hd] at hpl
          obtain ⟨x, y, z, rfl⟩ := ind_ind b v d' e' hd
          simp only [← hpl, okW, (lt_toUInt64_iff _ _).mp hie, ↓reduceIte]
          exact declLine_link' e' false ik idx (.decl (.ind x y z)) _ r e h
            ⟨⟨rfl, v, rfl, e', hd⟩, fun d hd => by cases hd; intro _ _ _ _ h'; cases h'⟩
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


end recordsS
end ConAgua.Front.FieldsLink

namespace L.Front
open ConAgua.Front.FieldsLink ConLeche.Frontend L.Front.Fields
open L.Scan.Line (scanLineLoop)

/-- **The `safety` converse on the declaration lines of `b`**: what `rec_decl_line` reads at a
line con-leche's loop reads as a declaration record satisfies `DeclSafeR'`. -/
def SafeLink' (b : ByteArray) : Prop :=
  ∀ (j : USize) (r : LineRec) (e : USize) (d : DeclRec),
    scanLineLoop b j true 0 0 .absent = .ok r e → (declLineN b.data j.toUInt64).pl ≠ 0 → r = .decl d →
      DeclSafeR' d (declLineN b.data j.toUInt64)

theorem safeLink' (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) :
    SafeLink' b := by
  intro j r e d h h0 hr
  exact declLine_link' b h64 hsize j true 0 0 .absent DFld.none r e h
    ⟨trivial, fun d hd => by cases hd⟩ h0 d hr

/-- **The scanner's `safety` converse** in the form `apply_decl`'s claim takes (`SafeLink`,
`DeclSafeR`: the same statement as `SafeLink'`, `DeclSafeR'`). -/
theorem safeLink (h64 : System.Platform.numBits = 64) (b : ByteArray) (hsize : b.size < 2 ^ 63) :
    SafeLink b := safeLink' h64 b hsize

end L.Front
