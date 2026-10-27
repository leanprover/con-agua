module

public import ConAgua.Scan.RecordsLink
public import ConAgua.Scan.Line
import ConAgua.Scan.LeafLink
import ConAgua.Scan.Link
import ConAgua.Scan.ValuesLink
import Std.Data.DTreeMap.Internal.Operations
import Std.Tactic.BVDecide.Normalize.Bool
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section
set_option linter.unusedSectionVars false


/-!
# The line and the driver, linked to con-leche

`scanLineLoop` against `lineN`, `scanLineFwd` against `lineFwdN`, and the driver `validN`
against `scanDriver`, a `Nat`-valued rendering of con-leche's `feedChunk`/`applyFinalLine` with
the semantic layer (`applyLine`) left out.
-/

namespace ConAgua.Scan.LineLink
open ConLeche.Frontend ConAgua.Scan ConAgua.Scan.RecordsLink
open L (Word)
open L.Scan.Utf8 (byteW)
open L.Scan.Member
open L.Scan.Records
open L.Scan.Line

/-- A line's payload as `lineN`'s `pl` code. -/
def plCode : LinePayload → Word
  | .absent => 0
  | .name _ => 1
  | .level _ => 2
  | .expr _ => 3
  | .decl _ => 4
  | .header => 5

theorem plCode_eq_zero (pl : LinePayload) : plCode pl = 0 ↔ pl.isAbsent = true := by
  cases pl <;> simp [plCode, LinePayload.isAbsent]

/-! ## `lineN` through `nextMemberN` -/

theorem lineN_congr (b : Array UInt8) (i w j w' idx pl : Word)
    (h : nextMemberN b i w = nextMemberN b j w') : lineN b i w idx pl = lineN b j w' idx pl := by
  conv => lhs; rw [lineN]
  conv => rhs; rw [lineN]
  simp only [h]

theorem lineN_key (b : Array UInt8) (i w idx pl p w' k v : Word)
    (h : nextMemberN b i w = ⟨2, p, w', k, v⟩) :
    lineN b i w idx pl =
      if k = 21 ∨ k = 19 ∨ k = 18 then
        (if idx ≠ 0 then 0
         else if p < L.Scan.Values.slotNatN b p v then
           lineN b (L.Scan.Values.slotNatN b p v) 0 (idxCode k) pl
         else 0)
      else if lineKind k = 0 then 0
      else if pl ≠ 0 then 0
      else if p < lineVal b k p v then lineN b (lineVal b k p v) 0 idx (lineKind k)
      else 0 := by
  have h0 : (nextMemberN b i w).tag ≠ 0 := by rw [h]; exact (by decide : (2 : Word) ≠ 0)
  have h1 : (nextMemberN b i w).tag ≠ 1 := by rw [h]; exact (by decide : (2 : Word) ≠ 1)
  by_cases hk : k = 21 ∨ k = 19 ∨ k = 18
  · rw [lineN_idx b i w idx pl h0 h1 (by rw [h]; exact hk), ite_eq_left hk, h]
  · rw [lineN_pay b i w idx pl h0 h1 (by rw [h]; exact hk), ite_eq_right hk, h]

/-! ## One key of the line -/

theorem lineStep_guard {c : Bool} {d : Prop} [Decidable d] {X : ScanRes LineRec} {Y : Word}
    {z : ScanErr} (hcd : c = true ↔ d) (hX : ¬ d → okW X = Y) :
    okW (if c = true then .err z else X) = if d then 0 else Y := by
  by_cases hc : c = true
  · rw [ite_eq_left hc, ite_eq_left (hcd.mp hc)]; rfl
  · rw [ite_eq_right hc, ite_eq_right (fun h => hc (hcd.mpr h))]; exact hX (fun h => hc (hcd.mpr h))

theorem idx_ne_iff (k : UInt8) : (k != 0) = true ↔ k.toUInt64 ≠ 0 := by
  rw [ne_eq, u8_toUInt64_eq k 0 (by decide)]; simp

theorem pl_ne_iff (pl : LinePayload) : (!pl.isAbsent) = true ↔ plCode pl ≠ 0 := by
  rw [ne_eq, plCode_eq_zero]; simp

theorem lineStep_lt {i e : USize} {G : ScanRes LineRec} {M : Word → Word} {y : ScanErr}
    (hG : i < e → okW G = M e.toUInt64) :
    okW (if i < e then G else .err y) = if i.toUInt64 < e.toUInt64 then M e.toUInt64 else 0 := by
  by_cases hie : i < e
  · rw [ite_eq_left hie, ite_eq_left ((lt_toUInt64_iff _ _).mp hie), hG hie]
  · rw [ite_eq_right hie, ite_eq_right (fun h => hie ((lt_toUInt64_iff _ _).mpr h))]; rfl

theorem lineStep_nz {i u : USize} {G : ScanRes LineRec} {M : Word → Word} {x y : ScanErr}
    (hG : i < u → okW G = M u.toUInt64) :
    okW (if u = 0 then .err x else if i < u then G else .err y) =
      if i.toUInt64 < u.toUInt64 then M u.toUInt64 else 0 := by
  by_cases hu : u = 0
  · subst hu; rw [ite_eq_left rfl]
    exact (ite_eq_right (show ¬ i.toUInt64 < USize.toUInt64 0 from UInt64.not_lt_zero)).symm
  · rw [ite_eq_right hu]; exact lineStep_lt hG

section steps
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lineStep_num {i v : USize} {G : ScanRes LineRec} {idxW plW : Word} {x y : ScanErr}
    (hG : i < numEnd b v → okW G = lineN b.data (numEnd b v).toUInt64 0 idxW plW) :
    okW (if numEnd b v = v then .err x else if i < numEnd b v then G else .err y) =
      if i.toUInt64 < L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64 then
        lineN b.data (L.Scan.Values.slotNatN b.data i.toUInt64 v.toUInt64) 0 idxW plW
      else 0 := by
  rw [slotNatN_link b h64 hsize]
  by_cases hn : numEnd b v = v
  · simp only [hn, ite_true]; exact (ite_eq_right UInt64.not_lt_zero).symm
  · simp only [hn, ite_false]
    rw [lineStep_lt (M := fun e => lineN b.data e 0 idxW plW) hG]
    by_cases hie : i < numEnd b v
    · simp [hie, (lt_toUInt64_iff _ _).mp hie]
    · simp [hie, UInt64.not_lt_zero]

/-- `meta`'s value: a braced value skipped. -/
theorem skip_link (v : USize) :
    (if v.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data v.toUInt64 = 123 then
      UInt64.ofNat (L.Examples.skipBracedN b.data (v.toUInt64 + 1).toNat 0) else 0) =
    if byteAt b v = 123 then (skipBraced b (v + 1) 0).toUInt64 else 0 := by
  by_cases h : v < b.usize
  · have hlt := (lt_usize_iff b h64 hsize v).mp h
    have hcw : byteW b.data v.toUInt64 = 123 ↔ byteAt b v = 123 := by
      rw [byteW_eq b h64 hsize]; exact u8_toUInt64_eq _ 123 (by decide)
    by_cases hc : byteAt b v = 123
    · rw [ite_eq_left ⟨hlt, hcw.mpr hc⟩, ite_eq_left hc, ← succ_toUInt64 b h64 hsize, USize.toNat_toUInt64,
        ← skipBraced_toNat_eq b h64 (by omega), ← toUInt64_eq_ofNat]
    · rw [ite_eq_right (fun h' => hc (hcw.mp h'.2)), ite_eq_right hc]
  · have h0 : byteAt b v = 0 := by unfold byteAt; rw [dite_eq_right h]
    rw [ite_eq_right (fun h' => h ((lt_usize_iff b h64 hsize v).mpr h'.1)), ite_eq_right (by rw [h0]; decide)]

theorem natListLoop_len (i : USize) (acc : List Nat) (w : Bool) (us : List Nat) (p : USize)
    (hacc : acc.length ≤ i.toNat) (h : scanNatListLoop b i acc w = .ok us p) : us.length ≤ p.toNat := by
  fun_induction scanNatListLoop b i acc w with
  | case1 i acc w hi c hws ih => exact ih (by have := usizeStep b i hi; omega) h
  | case2 i acc w hi c hws h93 hw => simp at h
  | case3 i acc w hi c hws h93 hw =>
    simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have := usizeStep b i hi; rw [List.length_reverse, this]; omega
  | case4 => simp at h
  | case5 i acc w hi c hws h93 h44 hw ih => exact ih (by have := usizeStep b i hi; omega) h
  | _ =>
    first
      | (simp at h; done)
      | (rename_i hj ih
         exact ih (by simp only [List.length_cons]; have := USize.lt_iff_toNat_lt.mp hj; omega) h)

theorem scanNatList_len (v : USize) (us : List Nat) (p : USize) (h : scanNatList b v = .ok us p) :
    us.length ≤ p.toNat := by
  unfold scanNatList at h
  split at h
  · exact natListLoop_len b h64 hsize _ _ _ _ _ (by simp) h
  · simp at h

end steps

section line
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

theorem lineLoop_link (i : USize) (w : Bool) (idxKind : UInt8) (idx : Nat) (pl : LinePayload) :
    okW (ConLeche.Frontend.scanLineLoop b i w idxKind idx pl) =
      lineN b.data i.toUInt64 (bw w) idxKind.toUInt64 (plCode pl) := by
  rw [ConLeche.Frontend.scanLineLoop.eq_def]
  by_cases h : i < b.usize
  · have hlt := (lt_usize_iff b h64 hsize i).mp h
    have hcw := byteW_eq b h64 hsize i
    have hs := succ_toUInt64 b h64 hsize i
    have hi1 : (i + 1).toNat = i.toNat + 1 := usizeStep b i h
    have hin := usizeInBounds b i h
    rw [dite_eq_left h]
    simp only [uget_byteAt _ i h]
    by_cases hws : isWs (byteAt b i) = true
    · simp only [hws, ite_true]
      rw [lineN_congr _ _ _ (i.toUInt64 + 1) (bw w), lineLoop_link (i + 1) w idxKind idx pl, hs]
      exact nextMemberN_ws _ _ _ hlt (by rw [hcw]; exact (ws_iff _).mp hws)
    have hws' : ¬ (byteW b.data i.toUInt64 = 32 ∨ byteW b.data i.toUInt64 = 9 ∨
        byteW b.data i.toUInt64 = 13) := by rw [hcw, ← ws_iff]; exact hws
    simp only [hws, Bool.false_eq_true, ite_false]
    by_cases h125 : byteAt b i = 125
    · have h125' : byteW b.data i.toUInt64 = 125 := by rw [hcw, h125]; rfl
      rw [lineN_close _ _ _ _ _ (by rw [nextMemberN_close _ _ _ hlt hws' h125'])]
      rw [nextMemberN_close _ _ _ hlt hws' h125', ← hs]
      simp only [h125, show ((125 : UInt8) == 125) = true from rfl, ite_true]
      have e0 : idxKind.toUInt64 = 0 ↔ idxKind = 0 := u8_toUInt64_eq idxKind 0 (by decide)
      have e1 : idxKind.toUInt64 = 1 ↔ idxKind = 1 := u8_toUInt64_eq idxKind 1 (by decide)
      have e2 : idxKind.toUInt64 = 2 ↔ idxKind = 2 := u8_toUInt64_eq idxKind 2 (by decide)
      have e3 : idxKind.toUInt64 = 3 ↔ idxKind = 3 := u8_toUInt64_eq idxKind 3 (by decide)
      simp only [e0, e1, e2, e3]
      cases pl <;> cases w <;> by_cases h0 : idxKind = 0 <;> by_cases h1 : idxKind = 1 <;>
        by_cases h2 : idxKind = 2 <;> by_cases h3 : idxKind = 3 <;>
        simp_all [bw, plCode, LinePayload.isAbsent, okW]
    have h125' : byteW b.data i.toUInt64 ≠ 125 := by
      rw [hcw]; exact fun h' => h125 ((u8_toUInt64_eq _ 125 (by decide)).mp h')
    simp only [show (byteAt b i == 125) = false by simpa using h125, Bool.false_eq_true, ite_false]
    by_cases h44 : byteAt b i = 44
    · have h44' : byteW b.data i.toUInt64 = 44 := by rw [hcw, h44]; rfl
      simp only [h44, show ((44 : UInt8) == 44) = true from rfl, ite_true]
      by_cases hw : w = true
      · rw [ite_eq_left hw, lineN_err _ _ _ _ _ (by
               rw [nextMemberN_comma _ _ _ hlt hws' h125' h44', ite_eq_left ((bw_ne_zero w).mpr hw)]; rfl)]
        rfl
      · rw [ite_eq_right hw, lineN_congr _ _ _ (i.toUInt64 + 1) 1,
          lineLoop_link (i + 1) true idxKind idx pl, hs]
        · rfl
        rw [nextMemberN_comma _ _ _ hlt hws' h125' h44', ite_eq_right (by rw [bw_ne_zero]; exact hw)]
    have h44' : byteW b.data i.toUInt64 ≠ 44 := by
      rw [hcw]; exact fun h' => h44 ((u8_toUInt64_eq _ 44 (by decide)).mp h')
    simp only [show (byteAt b i == 44) = false by simpa using h44, Bool.false_eq_true, ite_false]
    by_cases h34 : byteAt b i = 34
    · have h34' : byteW b.data i.toUInt64 = 34 := by rw [hcw, h34]; rfl
      have hq := nextMemberN_quote_link b h64 hsize i (bw w) h h34
      simp only [h34, show ((34 : UInt8) == 34) = true from rfl, ite_true]
      by_cases hbad : w = false ∨ keyEnd b (i + 1) = 0 ∨ valueAt b i (keyEnd b (i + 1)) = i
      · have h0 : (nextMemberN b.data i.toUInt64 (bw w)).tag = 0 := by
          rw [hq]
          rcases hbad with hb | hb | hb
          · subst hb; rfl
          · simp [hb]; rfl
          · simp [hb]; rfl
        rw [lineN_err _ _ _ _ _ h0]
        rcases hbad with hb | hb | hb
        · subst hb; rfl
        · simp only [hb, beq_self_eq_true, ite_true]; split <;> rfl
        · simp only [hb, beq_self_eq_true, ite_true]; (repeat' split) <;> rfl
      simp only [not_or] at hbad
      obtain ⟨hw, hk, hv⟩ := hbad
      have hw' : w = true := by simpa using hw
      subst hw'
      simp only [bw, ite_true, show (1 : Word) ≠ 0 by decide, ite_false, hk, hv] at hq
      simp only [bw, ite_true]
      rw [lineN_key _ _ _ _ _ _ _ _ _ hq]
      simp only [Bool.not_true, Bool.false_eq_true, ite_false, hk, hv, beq_iff_eq]
      generalize valueAt b i (keyEnd b (i + 1)) = v
      generalize keyAt b i (keyEnd b (i + 1) - (i + 1)) = K
      cases K
      all_goals dsimp only
      all_goals simp (config := {decide := true}) only [lineKind, lineVal, idxCode, ↓reduceIte]
      all_goals (try simp only [dite_eq_ite])
      all_goals first
        | rfl
        | (apply lineStep_guard (idx_ne_iff idxKind)
           intro _
           apply lineStep_num b h64 hsize
           exact fun hie => lineLoop_link (numEnd b v) false _ _ _)
        | (apply lineStep_guard (pl_ne_iff pl)
           intro _
           first
             | (apply lineStep_num b h64 hsize
                exact fun hie => lineLoop_link (numEnd b v) false _ _ _)
             | (rw [skip_link b h64 hsize v]
                by_cases hc : byteAt b v = 123
                · simp only [hc, bne_self_eq_false, Bool.false_eq_true, ite_false, ite_true]
                  apply lineStep_nz (M := fun x => lineN b.data x 0 _ _)
                  exact fun hie => lineLoop_link _ false _ _ _
                · have hc' : (byteAt b v != 123) = true := by simpa using hc
                  simp only [hc, hc', ite_true, ite_false]
                  exact (ite_eq_right UInt64.not_lt_zero).symm)
             | (rw [← natList_link b h64 hsize v]
                split
                · rename_i heq; rw [heq]; simp [encNL, okW]
                · rename_i us e heq
                  have hlen := scanNatList_len b h64 hsize v us e heq
                  rw [heq]; simp only [encNL]
                  split
                  · by_cases he0 : e.toUInt64 = 0
                    · have hie : ¬ i < e := by
                        rw [lt_toUInt64_iff, he0]; exact UInt64.not_lt_zero
                      simp only [he0, ite_true, hie, ite_false]
                      exact (ite_eq_right UInt64.not_lt_zero).symm
                    · simp only [he0, ite_false, List.length_cons, List.length_nil]
                      simp only [show UInt64.ofNat (0 + 1 + 1) = (2 : Word) from rfl, ite_true]
                      apply lineStep_lt (M := fun x => lineN b.data x 0 _ _)
                      exact fun hie => lineLoop_link _ false _ _ _
                  · rename_i hne
                    have heU : e.toNat < 2 ^ 64 := by rw [← usize_size_eq64 h64]; exact e.toNat_lt_size
                    have h2 : UInt64.ofNat us.length ≠ 2 := by
                      intro h2
                      have hl : us.length = 2 := by
                        have := congrArg UInt64.toNat h2
                        rw [UInt64.toNat_ofNat_of_lt' (by
                          have hU : UInt64.size = 2 ^ 64 := rfl
                          rw [hU]; omega)] at this
                        exact this
                      match us, hl with
                      | [a, d], _ => exact hne a d rfl
                    simp only [h2, ite_false, ite_self]
                    exact (ite_eq_right UInt64.not_lt_zero).symm)
             | (rw [← lam_link b h64 hsize v]  -- before the group: `forall_link` has the same right side
                split
                · rename_i heq; rw [heq]; simp only [okW]; exact (ite_eq_right UInt64.not_lt_zero).symm
                · rename_i heq; rw [heq]; simp only [okW]
                  apply lineStep_lt (M := fun x => lineN b.data x 0 _ _)
                  exact fun hie => lineLoop_link _ false _ _ _)
             | ((first
                 | rw [← strName_link b h64 hsize v]
                 | rw [← numName_link b h64 hsize v]
                 | rw [← app_link b h64 hsize v]
                 | rw [← forall_link b h64 hsize v]
                 | rw [← letE_link b h64 hsize v]
                 | rw [← constE_link b h64 hsize v]
                 | rw [← proj_link b h64 hsize v]
                 | rw [← axiomD_link b h64 hsize v]
                 | rw [← defD_link b h64 hsize v]
                 | rw [← thmD_link b h64 hsize v]
                 | rw [← opaqueD_link b h64 hsize v]
                 | rw [← quotD_link b h64 hsize v]
                 | rw [← indD_link b h64 hsize v]
                 | rw [← scanString_link b h64 hsize v]
                 | rw [← scanQuotedNat_eq_quotedNatN b h64 hsize v])
                split
                · rename_i heq; rw [heq]; simp only [okW]; exact (ite_eq_right UInt64.not_lt_zero).symm
                · rename_i heq; rw [heq]; simp only [okW]
                  apply lineStep_lt (M := fun x => lineN b.data x 0 _ _)
                  exact fun hie => lineLoop_link _ false _ _ _)
             )
    · have h34' : byteW b.data i.toUInt64 ≠ 34 := by
        rw [hcw]; exact fun h' => h34 ((u8_toUInt64_eq _ 34 (by decide)).mp h')
      simp only [show (byteAt b i == 34) = false by simpa using h34, Bool.false_eq_true, ite_false]
      rw [lineN_err _ _ _ _ _ (by rw [nextMemberN_other _ _ _ hlt hws' h125' h44' h34']; rfl)]; rfl
  · rw [dite_eq_right h, lineN_err _ _ _ _ _ (by
            rw [nextMemberN_end _ _ _ (by rw [← lt_usize_iff b h64 hsize]; exact h)]; rfl)]; rfl
termination_by b.size - i.toNat
decreasing_by
  all_goals first
    | omega
    | (have := USize.lt_iff_toNat_lt.mp ‹_›; omega)

omit h64 hsize in
/-- A line's members end past where they started. -/
theorem lineLoop_pos (i : USize) (w : Bool) (k : UInt8) (idx : Nat) (pl : LinePayload)
    (r : LineRec) (j : USize) (h : ConLeche.Frontend.scanLineLoop b i w k idx pl = .ok r j) :
    i.toNat < j.toNat := by
  fun_induction ConLeche.Frontend.scanLineLoop b i w k idx pl generalizing r j
  all_goals first
    | (simp at h; done)
    | (rename_i ih; have := ih _ _ h; have := usizeStep b _ ‹_ < b.usize›; omega)
    | (rename_i hj ih; have := ih _ _ h; have := USize.lt_iff_toNat_lt.mp hj; omega)
    | (simp only [ScanRes.ok.injEq] at h; obtain ⟨-, rfl⟩ := h; have := usizeStep b _ ‹_ < b.usize›; omega)
    | (rename_i ih; have := ih _ _ h; simp only [USize.lt_iff_toNat_lt] at *; omega)

/-! ## `scanLineFwd` -/

/-- A line's result as `lineFwdN`'s pair: `(1, next)` or `(0, 0)`. -/
def encLine {α : Type} : ScanRes α → Word × Word
  | .ok _ p => (1, p.toUInt64)
  | .err _ => (0, 0)

theorem usize_le_iff (p : USize) : b.usize ≤ p ↔ UInt64.ofNat b.data.size ≤ p.toUInt64 := by
  rw [← Decidable.not_iff_not, USize.not_le, UInt64.not_le]
  exact lt_usize_iff b h64 hsize p

theorem nl_iff (p : USize) :
    (byteAt b p == 10) = true ↔ (p.toUInt64 < UInt64.ofNat b.data.size ∧ byteW b.data p.toUInt64 = 10) := by
  rw [byteW_eq b h64 hsize, u8_toUInt64_eq _ 10 (by decide), ← lt_usize_iff b h64 hsize]
  rw [beq_iff_eq]
  by_cases h : p < b.usize
  · exact ⟨fun h1 => ⟨h, h1⟩, fun h1 => h1.2⟩
  · have h0 : byteAt b p = 0 := by unfold byteAt; rw [dite_eq_right h]
    exact ⟨fun h1 => absurd (h0.symm.trans h1) (by decide), fun h1 => absurd h1.1 h⟩

/-- After the closing brace. -/
theorem lineEnd_link {r : LineRec} {z : ScanErr} (p : USize) :
    encLine (if (byteAt b p == 10) = true then .ok r (p + 1)
      else if b.usize ≤ p then .ok r 0 else .err z) =
    lineFwdN.lineEndN b.data p.toUInt64 := by
  unfold lineFwdN.lineEndN
  by_cases h1 : (byteAt b p == 10) = true
  · rw [ite_eq_left h1, ite_eq_left ((nl_iff b h64 hsize p).mp h1), ← succ_toUInt64 b h64 hsize]; rfl
  · rw [ite_eq_right h1, ite_eq_right (fun h => h1 ((nl_iff b h64 hsize p).mpr h))]
    by_cases h2 : b.usize ≤ p
    · rw [ite_eq_left h2, ite_eq_left ((usize_le_iff b h64 hsize p).mp h2)]; rfl
    · rw [ite_eq_right h2, ite_eq_right (fun h => h2 ((usize_le_iff b h64 hsize p).mpr h))]; rfl

/-- con-leche's `scanLineFwd` against `lineFwdN`: the line's verdict and where the next one
starts. -/
theorem lineFwd_link (i : USize) : encLine (scanLineFwd b i) = lineFwdN b.data i.toUInt64 := by
  unfold scanLineFwd lineFwdN
  rw [USize.toNat_toUInt64, ← skipWs_toUInt64_eq b h64 (by omega)]
  generalize skipWs b i = s
  unfold lineFwdN.lineFwd2N
  simp only []
  by_cases h1 : (byteAt b s == 10) = true
  · rw [ite_eq_left h1, ite_eq_left ((nl_iff b h64 hsize s).mp h1), ← succ_toUInt64 b h64 hsize]; rfl
  rw [ite_eq_right h1, ite_eq_right (fun h => h1 ((nl_iff b h64 hsize s).mpr h))]
  by_cases h2 : b.usize ≤ s
  · rw [ite_eq_left h2, ite_eq_left ((usize_le_iff b h64 hsize s).mp h2)]; rfl
  rw [ite_eq_right h2, ite_eq_right (fun h => h2 ((usize_le_iff b h64 hsize s).mpr h))]
  have hs : s < b.usize := by rw [← USize.not_le]; exact h2
  have hc : (byteAt b s != 123) = true ↔ byteW b.data s.toUInt64 ≠ 123 := by
    rw [byteW_eq b h64 hsize, ne_eq, u8_toUInt64_eq _ 123 (by decide)]; simp
  by_cases h3 : (byteAt b s != 123) = true
  · rw [ite_eq_left h3, ite_eq_left (hc.mp h3)]; rfl
  rw [ite_eq_right h3, ite_eq_right (fun h => h3 (hc.mpr h))]
  have hl := lineLoop_link b h64 hsize (s + 1) true 0 0 .absent
  rw [succ_toUInt64 b h64 hsize] at hl
  have hl' : lineLoopN b.data (s.toUInt64 + 1) = okW (scanLineLoop b (s + 1) true 0 0 .absent) := by
    rw [hl]; rfl
  rw [hl']
  cases hr : scanLineLoop b (s + 1) true 0 0 .absent with
  | err e => rfl
  | ok r j =>
    have hpos := lineLoop_pos b (s + 1) true 0 0 .absent r j hr
    have hj : j.toUInt64 ≠ 0 := by
      intro h0; rw [← USize.toNat_toUInt64 j, h0] at hpos; simp at hpos
    simp only [okW, hj, ite_false]
    rw [USize.toNat_toUInt64, ← skipWs_toUInt64_eq b h64 (by omega)]
    exact lineEnd_link b h64 hsize _

end line

/-! ## The driver -/

section driver
variable (b : ByteArray) (h64 : System.Platform.numBits = 64) (hsize : b.size < 2 ^ 63)
include h64 hsize

end driver

end ConAgua.Scan.LineLink
