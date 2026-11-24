module

public import ConAgua.Arena.FreezeCmpSpec
import all ConAgua.Arena.FreezeCmp

@[expose] public section

/-!
# The compared run's buffer through its two headers (lane compare, design (i))

After mode `7` (`check_c3(1)`: `par_compact(1, hdrW)` on the memory `m9` at the challenge's index,
then `cmp_hdr_s`), `OUT` holds one buffer of `word 1` words with two headers:

* `cmpBufC OUT mc` (from header C at word `5` of header S): `HdrView … m9`, word `5` zero:
  `cmpView_C` (header C's view is the flat mode's view of `m9`);
* `cmpBufS OUT mc` (from word `0`): `HdrView … (viewS m9)`, word `5` = `hdrW`: `cmpView_S`.
-/

namespace L.Arena

open L

/-- The whole buffer: `OUT`'s first `word 1` words. -/
def cmpBufS (out : ArrId) (m : Mem) : Array Word := (m.arr64 out).extract 0 ((m.arr64 out).getD 1 0).toNat

/-- The buffer from header C (at word `5` of the whole buffer). -/
def cmpBufC (out : ArrId) (m : Mem) : Array Word :=
  (cmpBufS out m).extract ((cmpBufS out m).getD 5 0).toNat (cmpBufS out m).size

/-! ## What `cmp_hdr_s` leaves of header C's buffer -/

theorem getD_set64_ne (M : Mem) (a : ArrId) (i v : Word) (k : Nat) (h : k ≠ i.toNat) :
    ((M.set64 a i v).arr64 a).getD k 0 = (M.arr64 a).getD k 0 := by
  rw [getD_set64_same, ite_eq_right (fun e => h e.1)]

theorem toNat_c (k : Nat) (h : k < 2 ^ 64) : (Nat.toUInt64 k).toNat = k := toNat_hdr k h

/-- One solution image (`b = 0`, `c = 1`) leaves the words below its offset but its header entry. -/
theorem fzStep_low (M : Mem) (i : Nat) (z : Fz) (o : Word) (hi : 11 + 2 * i < 2 ^ 64)
    (hz : z.src ≠ OUT) (hok : fzOK M 1 i z o 0 = true) (hlt : (M.arr64 OUT).size < 2 ^ 64)
    (k : Nat) (hk : k < o.toNat) (h10 : k ≠ 10 + 2 * i) (h11 : k ≠ 11 + 2 * i) :
    ((fzStep M 1 i z o 0).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  simp only [fzOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, hc⟩, -⟩, -⟩ := hok
  have hc' : (0 + o).toNat + (fzEv M z.e).toNat ≤ (M.arr64 OUT).size ∧ (fzEv M z.e).toNat ≤ (M.arr64 z.src).size := by
    rcases hc with h | h
    · exact absurd h (by decide)
    · exact h
  have e0 : (0 + o) = o := by simp
  rw [e0] at hc'
  have i10 : ((0 : Word) + (10 + 2 * i).toUInt64).toNat = 10 + 2 * i := by
    rw [UInt64.zero_add, toNat_c _ (by omega)]
  have i11 : ((0 : Word) + (11 + 2 * i).toUInt64).toNat = 11 + 2 * i := by
    rw [UInt64.zero_add, toNat_c _ (by omega)]
  simp only [fzStep, fzCopy, e0]
  rw [getD_set64_ne _ _ _ _ _ (by rw [i11]; exact h11), getD_set64_ne _ _ _ _ _ (by rw [i10]; exact h10),
    ite_eq_left (by decide : (1 : Word) ≠ 0)]
  have := (fzEv M z.e).toNat_lt
  rw [getD_copy64 (Ne.symm hz) _ _ _ _ (by omega) (by simp; omega), ite_eq_right (by omega)]

theorem fzOK_fit (M : Mem) (i : Nat) (z : Fz) (o : Word) (hok : fzOK M 1 i z o 0 = true) :
    o.toNat + (fzEv M z.e).toNat ≤ (M.arr64 OUT).size := by
  simp only [fzOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, hc⟩, -⟩, -⟩ := hok
  rcases hc with h | h
  · exact absurd h (by decide)
  · simpa using h.1

/-- **The solution's images leave the words from `lo` to their first offset** (their header
entries lie below `lo`), and the offsets grow without wrapping. -/
theorem xsGo_low (lo : Nat) : ∀ (xs : List (Nat × Fz)) (M : Mem) (o : Word),
    (∀ x ∈ xs, x.2.src ≠ OUT ∧ 12 + 2 * x.1 ≤ lo) → xsOK xs M o = true → (M.arr64 OUT).size < 2 ^ 64 →
    ((xsGo xs M o).1.arr64 OUT).size = (M.arr64 OUT).size ∧
    o.toNat ≤ (xsGo xs M o).2.toNat ∧ (xsGo xs M o).2.toNat ≤ max o.toNat (M.arr64 OUT).size ∧
    ∀ k, lo ≤ k → k < o.toNat → ((xsGo xs M o).1.arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0
  | [], M, o, _, _, _ => ⟨rfl, Nat.le_refl _, Nat.le_max_left _ _, fun _ _ _ => rfl⟩
  | (i, z) :: xs, M, o, h, hok, hlt => by
    simp only [xsOK, Bool.and_eq_true] at hok
    have hx := h (i, z) (by simp)
    have hfit := fzOK_fit M i z o hok.1
    have hF := OutFrame.fzStep M 1 i z o 0
    have hlt' : ((fzStep M 1 i z o 0).arr64 OUT).size < 2 ^ 64 := by rw [hF.size]; exact hlt
    obtain ⟨ih1, ih2, ih3, ih4⟩ := xsGo_low lo xs (fzStep M 1 i z o 0) (o + fzEv M z.e)
      (fun y hy => h y (by simp [hy])) hok.2 hlt'
    have ho : (o + fzEv M z.e).toNat = o.toNat + (fzEv M z.e).toNat := toNat_add_lt _ _ (by omega)
    simp only [xsGo]
    rw [hF.size] at ih1 ih3
    refine ⟨ih1, by omega, by omega, fun k hk1 hk2 => ?_⟩
    rw [ih4 k hk1 (by omega), fzStep_low M i z o (by omega) hx.1 hok.1 hlt k hk2 (by omega) (by omega)]

/-- Header S's entries leave every word from `hdrW` on. -/
theorem hsMem_high : ∀ (is : List Nat) (M : Mem), (∀ i ∈ is, i < frozen.length) →
    ((hsMem M is).arr64 OUT).size = (M.arr64 OUT).size ∧
    ∀ k, hdrW ≤ k → ((hsMem M is).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0
  | [], M, _ => ⟨rfl, fun _ _ => rfl⟩
  | i :: is, M, h => by
    have hi := h i (by simp)
    obtain ⟨ih1, ih2⟩ := hsMem_high is (hsStep M i) (fun j hj => h j (by simp [hj]))
    have hfl := frozen_length
    have hhw := hdrW_eq
    simp only [hsMem]
    refine ⟨by rw [ih1, (OutFrame.hsStep M i).size], fun k hk => ?_⟩
    rw [ih2 k hk]
    unfold hsStep
    split
    · rw [getD_set64_ne _ _ _ _ _ (by rw [toNat_c _ (by omega)]; omega),
        getD_set64_ne _ _ _ _ _ (by rw [toNat_c _ (by omega)]; omega)]
    · rfl

theorem seedFold_low (so : Word) (lo : Nat) (hso : so.toNat + 224 < 2 ^ 64) (hlo : lo ≤ so.toNat) :
    ∀ (ks : List Nat) (M : Mem), (∀ k ∈ ks, k < 224) →
    ∀ k, k < lo → ((ks.foldl (seedPut so) M).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0
  | [], _, _, _, _ => rfl
  | j :: ks, M, h, k, hk => by
    have hj := h j (by simp)
    rw [List.foldl_cons, seedFold_low so lo hso hlo ks _ (fun x hx => h x (by simp [hx])) k hk, seedPut,
      getD_set64_ne _ _ _ _ _ (by rw [toNat_badd _ _ (by omega)]; omega)]

/-- The seed's patches leave every word below the seed's offset. -/
theorem seedMem_low (M : Mem) (so : Word) (hso : so.toNat + 224 < 2 ^ 64) (k : Nat) (hk : k < so.toNat) :
    ((seedMem M so).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  have hW : ∀ k ∈ hsSeedW, k < 224 := by decide
  simp only [seedMem]
  rw [getD_set64_ne _ _ _ _ _ (by rw [toNat_badd _ _ (by omega)]; omega),
    seedFold_low so so.toNat hso (Nat.le_refl _) hsSeedW _ hW k hk,
    getD_set64_ne _ _ _ _ _ (by rw [toNat_badd _ _ (by omega)]; omega)]

/-- Header S's words leave every word from `10` on. -/
theorem hsTail_high (M : Mem) (o : Word) (k : Nat) (hk : 10 ≤ k) :
    ((hsTail M o).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  simp only [hsTail]
  repeat rw [getD_set64_ne _ _ _ _ _ (by rw [toNat_c _ (by omega)]; omega)]

theorem hsTail_words (M : Mem) (o : Word) (h : 9 < (M.arr64 OUT).size) :
    ((hsTail M o).arr64 OUT).getD 0 0 = fzMagic ∧ ((hsTail M o).arr64 OUT).getD 1 0 = o ∧
    ((hsTail M o).arr64 OUT).getD 2 0 = rd64 M L.Checker.SDECL 0 ∧
    ((hsTail M o).arr64 OUT).getD 3 0 = rd64 M CTL 225 ∧
    ((hsTail M o).arr64 OUT).getD 4 0 = UInt64.ofNat frozen.length ∧
    ((hsTail M o).arr64 OUT).getD 5 0 = hdrWW ∧
    ((hsTail M o).arr64 OUT).getD 8 0 = 0 ∧ ((hsTail M o).arr64 OUT).getD 9 0 = hdrWW := by
  simp only [hsTail, getD_set64_same, L.Mem.size64_set64]
  simp (config := { decide := true }) [show 0 < (M.arr64 OUT).size by omega,
    show 1 < (M.arr64 OUT).size by omega, show 2 < (M.arr64 OUT).size by omega,
    show 3 < (M.arr64 OUT).size by omega, show 4 < (M.arr64 OUT).size by omega,
    show 5 < (M.arr64 OUT).size by omega, show 8 < (M.arr64 OUT).size by omega, h, hdrWW, hdrW_eq]
  all_goals rfl

theorem hsTail_size (M : Mem) (o : Word) : ((hsTail M o).arr64 OUT).size = (M.arr64 OUT).size := by
  simp only [hsTail, L.Mem.size64_set64]

theorem seedMem_size (M : Mem) (so : Word) : ((seedMem M so).arr64 OUT).size = (M.arr64 OUT).size := by
  simp only [seedMem, L.Mem.size64_set64, (OutFrame.seedFold so hsSeedW _).size]

section views
variable {m9 : Mem}

/-- The facts both views use: the sizes, header C's buffer's offsets, and the whole buffer's
length `T`. -/
theorem cmpC_facts (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64)
    (hS : CmpHdrSOK (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) :
    let M := parCompactMem m9 1 hdrWW
    let lc := fzOff m9 frozen.length
    let o0 := hdrW.toUInt64 + lc
    let mc := cmpHdrSMem M lc
    (mc.arr64 OUT).size = (m9.arr64 OUT).size ∧
    o0.toNat = hdrW + lc.toNat ∧ lc.toNat = hdrW + fzSum m9 frozen.length ∧
    o0.toNat + 256 ≤ (m9.arr64 OUT).size ∧
    o0.toNat ≤ (hsImgs M lc).2.toNat ∧ (hsImgs M lc).2.toNat ≤ (m9.arr64 OUT).size ∧
    (mc.arr64 OUT).getD 1 0 = (hsImgs M lc).2 ∧ (mc.arr64 OUT).getD 5 0 = hdrWW ∧
    ∀ k, hdrW ≤ k → k < o0.toNat → (mc.arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  intro M lc o0 mc
  have hhw := hdrW_eq
  have hfl := frozen_length
  have hb : hdrWW.toNat + hdrW < 2 ^ 64 := by simp [hdrWW]; omega
  have hb' : hdrWW.toNat = hdrW := by simp [hdrWW]; omega
  have hW := parCompactOK_hdr_b hok hb
  have hg : (∀ j ≤ frozen.length, (fzOff m9 j).toNat = hdrW + fzSum m9 j) ∧
      hdrWW.toNat + hdrW + fzSum m9 frozen.length ≤ (m9.arr64 OUT).size := by
    have h' := hok
    simp only [parCompactOK, Bool.and_eq_true] at h'
    exact (pcGo_good m9 1 hdrWW hW hb (fun _ => hlt) frozen.length (Nat.le_refl _) h'.1.1.1).1 one_ne_zero'
  have hlc : lc.toNat = hdrW + fzSum m9 frozen.length := hg.1 _ (Nat.le_refl _)
  have hMs : (M.arr64 OUT).size = (m9.arr64 OUT).size := (parCompactMem_out_b m9 1 hdrWW).size OUT
  have ho0 : o0.toNat = hdrW + lc.toNat := by
    show (hdrW.toUInt64 + lc).toNat = _
    rw [UInt64.toNat_add, toNat_c _ (by omega)]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨hM1s, hM1k⟩ := hsMem_high (List.range frozen.length) M (fun i hi => List.mem_range.mp hi)
  have hxs : ∀ x ∈ xsL, x.2.src ≠ OUT ∧ 12 + 2 * x.1 ≤ hdrW := by
    intro x hx
    have := List.all_eq_true.mp xsL_ok x hx
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
    refine ⟨this.2, ?_⟩
    simp only [xsL, fzsImgs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> decide
  have hlt1 : ((hsMem M (List.range frozen.length)).arr64 OUT).size < 2 ^ 64 := by rw [hM1s, hMs]; exact hlt
  obtain ⟨hXs, hX1, hX2, hXk⟩ := xsGo_low hdrW xsL _ o0 hxs hS.1 hlt1
  have h256 : o0.toNat + 256 ≤ (m9.arr64 OUT).size := by
    have h1 := hS.1
    simp only [xsL, xsOK, Bool.and_eq_true] at h1
    have := fzOK_fit _ _ _ _ h1.1
    rw [hM1s, hMs] at this
    exact this
  have hsz : (mc.arr64 OUT).size = (m9.arr64 OUT).size := by
    show ((cmpHdrSMem M lc).arr64 OUT).size = _
    rw [cmpHdrSMem, hsTail_size, seedMem_size, hsImgs, hXs, hM1s, hMs]
  have h9 : 9 < ((seedMem (hsImgs M lc).1 o0).arr64 OUT).size := by
    rw [seedMem_size, hsImgs, hXs, hM1s, hMs]; omega
  have hT := hsTail_words _ (hsImgs M lc).2 h9
  refine ⟨hsz, ho0, hlc, h256, ?_, ?_, hT.2.1, hT.2.2.2.2.2.1, fun k hk1 hk2 => ?_⟩
  · exact hX1
  · have := hX2; rw [hM1s, hMs] at this; exact Nat.le_trans this (Nat.max_le.mpr ⟨by omega, Nat.le_refl _⟩)
  · show ((cmpHdrSMem M lc).arr64 OUT).getD k 0 = _
    rw [cmpHdrSMem, hsTail_high _ _ k (by omega), seedMem_low _ _ (by omega) k hk2, hsImgs, hXk k hk1 hk2,
      hM1k k hk1]

/-- **Header C's view**: the buffer from header C shows the challenge's memory `m9` (as the flat
mode's buffer shows its memory), with no next phase. -/
theorem cmpView_C (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64)
    (hS : CmpHdrSOK (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) :
    HdrView (cmpBufC OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))) m9 ∧
    (cmpBufC OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).getD 5 0 = 0 := by
  obtain ⟨hsz, ho0, hlc, h256, hX1, hX2, h1, h5, hk⟩ := cmpC_facts hok hlt hS
  generalize hmc : cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length) = mc at *
  generalize hT : (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2 = T at *
  have hhw := hdrW_eq
  have hb : hdrWW.toNat + hdrW < 2 ^ 64 := by simp [hdrWW]; omega
  have hb' : hdrWW.toNat = hdrW := by simp [hdrWW]; omega
  have hSz : (cmpBufS OUT mc).size = T.toNat := by
    simp only [cmpBufS, h1, Array.size_extract]; omega
  have hSg : ∀ k < T.toNat, (cmpBufS OUT mc).getD k 0 = (mc.arr64 OUT).getD k 0 := by
    intro k hk'
    simp only [cmpBufS, h1]
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add]
  have h5' : (cmpBufS OUT mc).getD 5 0 = hdrWW := by rw [hSg 5 (by omega), h5]
  have hCg : ∀ k, hdrW + k < T.toNat →
      (cmpBufC OUT mc).getD k 0 = (mc.arr64 OUT).getD (hdrW + k) 0 := by
    intro k hk'
    simp only [cmpBufC, h5', hb']
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract, hSz]; omega), hSg _ hk']
  have hCs : (cmpBufC OUT mc).size = T.toNat - hdrW := by
    simp only [cmpBufC, h5', hb', Array.size_extract, hSz]; omega
  have hM := parCompactMem_hdr_b hok hb
  refine ⟨hdrView_of _ hok hb hlt (fun k hk' => ?_) (by rw [hCs]; omega), ?_⟩
  · rw [hCg k (by omega), hk _ (by omega) (by omega), hb']
  · rw [hCg 5 (by omega), hk _ (by omega) (by omega), ← hb']; exact hM.2.2.2.2.2.1

end views

/-! ## Header S's view: the solution's phase -/

/-- The solution's seed in `CTL`: word `128` := `CTL[225]` (the solution's index counter),
`162‥173` := `SCTL`'s, `224` := `0` (no solution). -/
def viewSCtl (m : Mem) : Array Word :=
  (hsSeedW.foldl (fun c k => c.setIfInBounds k ((m.arr64 L.Checker.SCTL).getD k 0))
    ((m.arr64 CTL).setIfInBounds 128 ((m.arr64 CTL).getD 225 0))).setIfInBounds 224 0

/-- **Header S's view of `m`**: the stream index's rows `EIX*`/`TIX*` are the solution's
`SIX*`/`STX*`, the records, firsts and declaration pool the solution's stashed `SDECL`, `SFIRSTS`,
`SDLP`, and `CTL` the solution's seed (`viewSCtl`); swapped, the solution's rows `SIX*`/`STX*` are
the challenge's `EIX*`/`TIX*` (header S points them at those images). -/
def viewSArr (m : Mem) (a : TieredArray) : Array Word :=
  if a = ↑EIXA then m.arr64 SIXA else if a = ↑EIXS then m.arr64 SIXS else if a = ↑EIXN then m.arr64 SIXN
  else if a = ↑TIXA then m.arr64 STXA else if a = ↑TIXS then m.arr64 STXS else if a = ↑TIXN then m.arr64 STXN
  else if a = ↑L.Front.DECL then m.arr64 L.Checker.SDECL else if a = ↑FIRSTS then m.arr64 L.Checker.SFIRSTS
  else if a = ↑L.Front.DLP then m.arr64 L.Checker.SDLP else if a = ↑CTL then viewSCtl m
  else if a = ↑SIXA then m.arr64 EIXA else if a = ↑SIXS then m.arr64 EIXS else if a = ↑SIXN then m.arr64 EIXN
  else if a = ↑STXA then m.arr64 TIXA else if a = ↑STXS then m.arr64 TIXS else if a = ↑STXN then m.arr64 TIXN
  else m.arr64 a

def viewS (m : Mem) : Mem := { m with words := viewSArr m }

/-- The arrays `viewS` changes. -/
def vsChg : List TieredArray := [↑EIXA, ↑EIXS, ↑EIXN, ↑TIXA, ↑TIXS, ↑TIXN, ↑L.Front.DECL, ↑FIRSTS, ↑L.Front.DLP, ↑CTL,
  ↑SIXA, ↑SIXS, ↑SIXN, ↑STXA, ↑STXS, ↑STXN]

theorem viewS_arr (m : Mem) (a : TieredArray) (h : a ∉ vsChg) : (viewS m).arr64 a = m.arr64 a := by
  simp only [vsChg, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := h
  simp only [viewS, Mem.arr64, viewSArr, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16,
    ite_false]

/-- The `CTL` words the seed's patches change. -/
def vsPatched (k : Nat) : Bool := k == 128 || (162 ≤ k && k ≤ 173) || k == 224

/-- An extent that reads nothing `viewS` changes. -/
def _root_.L.Expr.vsOk : Expr → Bool
  | .const _ => true
  | .bin _ a b => a.vsOk && b.vsOk
  | .ld64 a (.const k) => (!(vsChg.contains ↑a)) || (a == CTL && !vsPatched k.toNat)
  | _ => false

theorem getD_setIB_ne (c : Array Word) (j k : Nat) (v : Word) (h : j ≠ k) :
    (c.setIfInBounds j v).getD k 0 = c.getD k 0 := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne h]

theorem viewSCtl_getD (m : Mem) (k : Nat) (hk : vsPatched k = false) :
    (viewSCtl m).getD k 0 = (m.arr64 CTL).getD k 0 := by
  have h1 : k ≠ 128 ∧ k ≠ 224 ∧ ¬(162 ≤ k ∧ k ≤ 173) := by
    simp only [vsPatched, Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq, Bool.and_eq_false_iff,
      decide_eq_false_iff_not] at hk
    omega
  have hf : ∀ (ks : List Nat) (c : Array Word), (∀ j ∈ ks, j ≠ k) →
      (ks.foldl (fun c j => c.setIfInBounds j ((m.arr64 L.Checker.SCTL).getD j 0)) c).getD k 0 = c.getD k 0 := by
    intro ks
    induction ks with
    | nil => intro c _; rfl
    | cons j ks ih =>
      intro c hj
      rw [List.foldl_cons, ih _ (fun x hx => hj x (by simp [hx])), getD_setIB_ne _ _ _ _ (hj j (by simp))]
  have hW : ∀ j ∈ hsSeedW, j ≠ k := by
    intro j hj
    simp only [hsSeedW, List.mem_map, List.mem_range] at hj
    omega
  unfold viewSCtl
  rw [getD_setIB_ne _ _ _ _ (Ne.symm h1.2.1), hf _ _ hW, getD_setIB_ne _ _ _ _ (Ne.symm h1.1)]

theorem viewSCtl_128 (m : Mem) (h : 128 < (m.arr64 CTL).size) :
    (viewSCtl m).getD (Nat.toUInt64 128).toNat 0 = (m.arr64 CTL).getD 225 0 := by
  have hf : ∀ (ks : List Nat) (c : Array Word), (∀ j ∈ ks, j ≠ 128) →
      (ks.foldl (fun c j => c.setIfInBounds j ((m.arr64 L.Checker.SCTL).getD j 0)) c).getD 128 0 = c.getD 128 0 := by
    intro ks
    induction ks with
    | nil => intro c _; rfl
    | cons j ks ih =>
      intro c hj
      rw [List.foldl_cons, ih _ (fun x hx => hj x (by simp [hx])), getD_setIB_ne _ _ _ _ (hj j (by simp))]
  have hW : ∀ j ∈ hsSeedW, j ≠ 128 := by decide
  rw [toNat_c _ (by omega)]
  unfold viewSCtl
  rw [getD_setIB_ne _ _ _ _ (by decide), hf _ _ hW, Array.getD_eq_getD_getElem?,
    Array.getElem?_setIfInBounds_self_of_lt h]
  rfl


theorem viewS_ctl (m : Mem) : (viewS m).arr64 ↑CTL = viewSCtl m := by
  simp only [viewS, Mem.arr64]
  unfold viewSArr
  rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
    ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

theorem fzEv_viewS (m : Mem) : ∀ (e : Expr), e.vsOk = true → fzEv (viewS m) e = fzEv m e
  | .const _, _ => rfl
  | .bin op a b, h => by
    simp only [Expr.vsOk, Bool.and_eq_true] at h
    rw [fzEv_bin, fzEv_bin, fzEv_viewS m a h.1, fzEv_viewS m b h.2]
  | .ld64 a i, h => by
    cases i with
    | const k =>
      rw [fzEv_ld64, fzEv_ld64]
      simp only [Expr.vsOk, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true, beq_iff_eq] at h
      have ek : fzEv (viewS m) (.const k) = k := rfl
      have ek' : fzEv m (.const k) = k := rfl
      rw [ek, ek']
      rcases h with h | ⟨rfl, h⟩
      · have hn : (a : TieredArray) ∉ vsChg := by
          intro hm; have := List.contains_iff_mem.mpr hm; rw [h] at this; cases this
        simp only [rd64, viewS_arr m _ hn]
      · simp only [rd64, viewS_ctl]
        exact viewSCtl_getD m _ h
    | _ => simp [Expr.vsOk] at h
  | .var _, h | .ld8 _ _, h | .len8 _, h | .len64 _, h | .cmpw _ _ _, h
  | .ldc _ _, h | .glob _, h | .ld64t _ _ _, h | .len64t _ _, h | .ld8x8 _ _, h | .ld32t _ _ _, h
  | .ld32h _ _ _ _, h => by simp [Expr.vsOk] at h

/-! ### The entries' classes -/

theorem hsE_same_all : (List.range frozen.length).all (fun i => match hsE i with
    | .same j => j != i || ((fzAt i).e.vsOk && !(vsChg.contains ↑(fzAt i).src))
    | _ => true) = true := by decide +kernel

/-- A header S entry that is header C's own: its source and extent are unchanged by `viewS`. -/
theorem same_self {i : Nat} (hi : i < frozen.length) (h : hsE i = .same i) :
    (fzAt i).e.vsOk = true ∧ ((fzAt i).src : TieredArray) ∉ vsChg := by
  have := List.all_eq_true.mp hsE_same_all i (List.mem_range.mpr hi)
  rw [h] at this
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at this
  exact ⟨this.1, fun hm => by rw [List.contains_iff_mem.mpr hm] at this; cases this.2⟩

/-- The rows header S swaps: (entry, header C's entry it takes, their sources, the count slot):
`EIX*`/`TIX*` take the solution's `SIX*`/`STX*`, and those take `EIX*`/`TIX*`. -/
def movedT : List (Nat × Nat × ArrId × ArrId × Nat) :=
  [(53, 63, EIXA, SIXA, nanonCS.ca.toNat), (54, 64, EIXS, SIXS, nstrCS.ca.toNat), (55, 65, EIXN, SIXN, nnumCS.ca.toNat),
   (56, 66, TIXA, STXA, nanonCS.ca.toNat), (57, 67, TIXS, STXS, nstrCS.ca.toNat), (58, 68, TIXN, STXN, nnumCS.ca.toNat),
   (63, 53, SIXA, EIXA, nanonCS.ca.toNat), (64, 54, SIXS, EIXS, nstrCS.ca.toNat), (65, 55, SIXN, EIXN, nnumCS.ca.toNat),
   (66, 56, STXA, TIXA, nanonCS.ca.toNat), (67, 57, STXS, TIXS, nstrCS.ca.toNat), (68, 58, STXN, TIXN, nnumCS.ca.toNat)]

/-- A swapped row's extent: twice its count, under the compare flag. -/
def rowExt (e : Expr) (ca : Nat) : Prop := e = .bin .mul (fzC 2) (fzCtl ca) ∨ e = fzSolExt ca

theorem movedT_hs : movedT.all (fun x => decide (hsE x.1 = .same x.2.1) &&
    decide ((fzAt x.1).src = x.2.2.1) && decide ((fzAt x.2.1).src = x.2.2.2.1) &&
    !vsPatched x.2.2.2.2 && decide (x.2.2.2.2 < 2 ^ 64)) = true := by decide +kernel

theorem movedT_e : ∀ x ∈ movedT, rowExt (fzAt x.1).e x.2.2.2.2 ∧ rowExt (fzAt x.2.1).e x.2.2.2.2 := by
  intro x hx
  simp only [movedT, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨.inl rfl, .inr rfl⟩ | exact ⟨.inr rfl, .inl rfl⟩

theorem movedT_ok : ∀ x ∈ movedT, hsE x.1 = .same x.2.1 ∧ (fzAt x.1).src = x.2.2.1 ∧
    (fzAt x.2.1).src = x.2.2.2.1 ∧ rowExt (fzAt x.1).e x.2.2.2.2 ∧ rowExt (fzAt x.2.1).e x.2.2.2.2 ∧
    vsPatched x.2.2.2.2 = false ∧ x.2.2.2.2 < 2 ^ 64 := by
  intro x hx
  have := List.all_eq_true.mp movedT_hs x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, (movedT_e x hx).1, (movedT_e x hx).2, this.1.2, this.2⟩

theorem hsE_moved_all : (List.range frozen.length).all (fun i => match hsE i with
    | .same j => j == i || movedT.any (·.1 == i) | _ => true) = true := by decide +kernel

theorem viewSArr_moved (m : Mem) : ∀ x ∈ movedT, viewSArr m ↑x.2.2.1 = m.arr64 x.2.2.2.1 := by
  intro x hx
  simp only [movedT, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [viewSArr] <;> rfl

theorem fzEv_ctl_viewS (m : Mem) (k : Nat) (hk : vsPatched k = false) (hk' : k < 2 ^ 64) :
    fzEv (viewS m) (fzCtl k) = fzEv m (fzCtl k) := by
  simp only [fzCtl, fzEv_ld64, rd64, viewS_ctl]
  have e : fzEv (viewS m) (.const k.toUInt64) = k.toUInt64 := rfl
  have e' : fzEv m (.const k.toUInt64) = k.toUInt64 := rfl
  rw [e, e', toNat_c _ hk']
  exact viewSCtl_getD m k hk

/-- **A header S entry taken from another header C entry** (the swapped rows): `viewS` shows
header C's image with its extent (the compare flag `CTL[cmpCW] = 1`). -/
theorem same_view (m : Mem) (h224 : rd64 m CTL (Nat.toUInt64 cmpCW) = 1) {i j : Nat} (hi : i < frozen.length)
    (hj : hsE i = .same j) :
    (viewS m).arr64 (fzAt i).src = m.arr64 (fzAt j).src ∧ fzEv (viewS m) (fzAt i).e = fzEv m (fzAt j).e := by
  have := List.all_eq_true.mp hsE_moved_all i (List.mem_range.mpr hi)
  rw [hj] at this
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at this
  rcases this with rfl | ⟨x, hx, hxi⟩
  · obtain ⟨h1, h2⟩ := same_self hi hj
    exact ⟨viewS_arr m _ h2, fzEv_viewS m _ h1⟩
  · obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := movedT_ok x hx
    have hxi' : x.1 = i := by simpa using hxi
    subst hxi'
    rw [hj] at h1
    cases h1
    rw [h2, h3]
    refine ⟨viewSArr_moved m x hx, ?_⟩
    have e : fzEv m (fzCtl cmpCW) = 1 := h224
    have ev : fzEv (viewS m) (fzCtl cmpCW) = 1 := by
      rw [fzEv_ctl_viewS m cmpCW (by decide) (by decide)]; exact e
    have e2 : fzEv (viewS m) (fzC 2) = fzEv m (fzC 2) := rfl
    have hc := fzEv_ctl_viewS m _ h6 h7
    have hr : ∀ (M : Mem) (f : Expr), fzEv M (fzCtl cmpCW) = 1 → rowExt f x.2.2.2.2 →
        fzEv M f = fzEv M (.bin .mul (fzC 2) (fzCtl x.2.2.2.2)) := by
      intro M f h1 hf
      rcases hf with rfl | rfl
      · rfl
      · simp only [fzSolExt, fzEv_bin, h1]; simp [BinOp.eval]
    rw [hr _ _ ev h4, hr _ _ e h5]
    simp only [fzEv_bin, hc, e2]

/-! ### Header S's entries in the final memory -/

/-- The value header S's entry `i` gets from header C's words in `M` (`none` for an image of its
own). -/
def hsVal (M : Mem) (i : Nat) : Option (Word × Word) :=
  match hsE i with
  | .same j => some (rd64 M OUT (hdrW + (10 + 2 * j)).toUInt64 + hdrW.toUInt64, rd64 M OUT (hdrW + (11 + 2 * j)).toUInt64)
  | .extra => none

theorem hsStep_other (M : Mem) (i : Nat) (hi : i < frozen.length) (k : Nat) (h10 : k ≠ 10 + 2 * i)
    (h11 : k ≠ 11 + 2 * i) : ((hsStep M i).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  have hfl := frozen_length
  unfold hsStep
  split
  · rw [getD_set64_ne _ _ _ _ _ (by rw [toNat_c _ (by omega)]; exact h11),
      getD_set64_ne _ _ _ _ _ (by rw [toNat_c _ (by omega)]; exact h10)]
  · rfl

theorem hsMem_other : ∀ (is : List Nat) (M : Mem) (k : Nat), (∀ i ∈ is, i < frozen.length) →
    (∀ i ∈ is, k ≠ 10 + 2 * i ∧ k ≠ 11 + 2 * i) →
    ((hsMem M is).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0
  | [], _, _, _, _ => rfl
  | i :: is, M, k, h, hk => by
    simp only [hsMem]
    rw [hsMem_other is _ k (fun j hj => h j (by simp [hj])) (fun j hj => hk j (by simp [hj])),
      hsStep_other M i (h i (by simp)) k (hk i (by simp)).1 (hk i (by simp)).2]

theorem hsVal_step (M : Mem) (i i' : Nat) (hi : i < frozen.length) (hi' : i' < frozen.length) :
    hsVal (hsStep M i') i = hsVal M i := by
  have hfl := frozen_length
  have hhw := hdrW_eq
  have hr : ∀ k, hdrW ≤ k → k < 2 ^ 64 → rd64 (hsStep M i') OUT k.toUInt64 = rd64 M OUT k.toUInt64 := by
    intro k hk hk'
    simp only [rd64, toNat_c _ hk']
    exact hsStep_other M i' hi' k (by omega) (by omega)
  unfold hsVal
  split
  · rename_i j hj; have := hsE_lt hi j hj
    rw [hr _ (by omega) (by omega), hr _ (by omega) (by omega)]
  · rfl

/-- **Header S's entry `i`** after `hsMem` (the list without repeats): header C's offset moved by
`hdrW`, its length (`0` for the solution's own rows). -/
theorem hsMem_entry : ∀ (is : List Nat) (M : Mem), is.Nodup → (∀ i ∈ is, i < frozen.length) →
    2 * hdrW ≤ (M.arr64 OUT).size → ∀ i ∈ is, ∀ v, hsVal M i = some v →
    ((hsMem M is).arr64 OUT).getD (10 + 2 * i) 0 = v.1 ∧ ((hsMem M is).arr64 OUT).getD (11 + 2 * i) 0 = v.2
  | [], _, _, _, _, i, hi, _, _ => absurd hi (by simp)
  | i0 :: is, M, hnd, h, hsz, i, hi, v, hv => by
    have hfl := frozen_length
    have hhw := hdrW_eq
    simp only [List.nodup_cons] at hnd
    simp only [hsMem]
    have hsz' : 2 * hdrW ≤ ((hsStep M i0).arr64 OUT).size := by rw [(OutFrame.hsStep M i0).size]; exact hsz
    rcases List.mem_cons.mp hi with rfl | hi'
    · have hn : ∀ j ∈ is, (10 + 2 * i ≠ 10 + 2 * j ∧ 10 + 2 * i ≠ 11 + 2 * j) ∧
          (11 + 2 * i ≠ 10 + 2 * j ∧ 11 + 2 * i ≠ 11 + 2 * j) := by
        intro j hj
        have : j ≠ i := fun e => hnd.1 (e ▸ hj)
        omega
      rw [hsMem_other is _ _ (fun j hj => h j (by simp [hj])) (fun j hj => (hn j hj).1),
        hsMem_other is _ _ (fun j hj => h j (by simp [hj])) (fun j hj => (hn j hj).2)]
      have hi0 := h i (by simp)
      unfold hsVal at hv
      unfold hsStep
      cases hE : hsE i with
      | same j =>
        simp only [hE, Option.some.injEq] at hv ⊢
        cases hv
        refine ⟨?_, ?_⟩
        · rw [getD_set64_ne _ _ _ _ _ (by rw [toNat_c _ (by omega)]; omega), getD_set64_same,
            ite_eq_left ⟨by rw [toNat_c _ (by omega)], by omega⟩]
        · rw [getD_set64_same, ite_eq_left ⟨by rw [toNat_c _ (by omega)], by simp only [L.Mem.size64_set64]; omega⟩]
      | extra => simp only [hE] at hv; cases hv
    · have := hsMem_entry is (hsStep M i0) hnd.2 (fun j hj => h j (by simp [hj])) hsz' i hi' v
        (by rw [hsVal_step _ _ _ (h i (by simp [hi'])) (h i0 (by simp))]; exact hv)
      exact this

/-! ### One solution image -/

theorem fzOK_parts (M : Mem) (i : Nat) (z : Fz) (o : Word) (hok : fzOK M 1 i z o 0 = true) :
    o.toNat + (fzEv M z.e).toNat ≤ (M.arr64 OUT).size ∧ (fzEv M z.e).toNat ≤ (M.arr64 z.src).size := by
  simp only [fzOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨-, hc⟩, -⟩, -⟩ := hok
  rcases hc with h | h
  · exact absurd h (by decide)
  · simpa using h

/-- **One solution image's header entry and words** (`b = 0`, `c = 1`, in bounds, `OUT` below `2^64`
words, the entry below the image). -/
theorem fzStep_put (M : Mem) (i : Nat) (z : Fz) (o : Word) (hz : z.src ≠ OUT) (hok : fzOK M 1 i z o 0 = true)
    (hlt : (M.arr64 OUT).size < 2 ^ 64) (hio : 12 + 2 * i ≤ o.toNat) :
    ((fzStep M 1 i z o 0).arr64 OUT).getD (10 + 2 * i) 0 = o ∧
    ((fzStep M 1 i z o 0).arr64 OUT).getD (11 + 2 * i) 0 = fzEv M z.e ∧
    ∀ t < (fzEv M z.e).toNat, ((fzStep M 1 i z o 0).arr64 OUT).getD (o.toNat + t) 0 = (M.arr64 z.src).getD t 0 := by
  obtain ⟨h1, h2⟩ := fzOK_parts M i z o hok
  have hsz := size_copy64 M OUT o z.src 0 (fzEv M z.e).toNat OUT
  have i10 : ((0 : Word) + (10 + 2 * i).toUInt64).toNat = 10 + 2 * i := by
    rw [UInt64.zero_add, toNat_c _ (by omega)]
  have i11 : ((0 : Word) + (11 + 2 * i).toUInt64).toNat = 11 + 2 * i := by
    rw [UInt64.zero_add, toNat_c _ (by omega)]
  have e0 : (0 + o) = o := by simp
  simp only [fzStep, fzCopy, e0, ite_eq_left (by decide : (1 : Word) ≠ 0)]
  have := (fzEv M z.e).toNat_lt
  refine ⟨?_, ?_, fun t ht => ?_⟩
  · rw [getD_set64_ne _ _ _ _ _ (by rw [i11]; omega), getD_set64_same, ite_eq_left ⟨by rw [i10], by rw [hsz]; omega⟩]
  · rw [getD_set64_same, ite_eq_left ⟨by rw [i11], by simp only [L.Mem.size64_set64, hsz]; omega⟩]
  · rw [getD_set64_ne _ _ _ _ _ (by rw [i11]; omega), getD_set64_ne _ _ _ _ _ (by rw [i10]; omega),
      getD_copy64 (Ne.symm hz) _ _ _ _ (by omega) (by simp; omega), ite_eq_left ⟨by omega, by omega, by omega⟩]
    congr 1; simp

/-- The solution's images keep every word below their first offset but their header entries. -/
theorem xsGo_keep : ∀ (xs : List (Nat × Fz)) (M : Mem) (o : Word),
    (∀ x ∈ xs, x.2.src ≠ OUT ∧ 12 + 2 * x.1 ≤ o.toNat) → xsOK xs M o = true → (M.arr64 OUT).size < 2 ^ 64 →
    ∀ k, k < o.toNat → (∀ x ∈ xs, k ≠ 10 + 2 * x.1 ∧ k ≠ 11 + 2 * x.1) →
    ((xsGo xs M o).1.arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0
  | [], _, _, _, _, _, _, _, _ => rfl
  | (i, z) :: xs, M, o, h, hok, hlt, k, hk, hne => by
    simp only [xsOK, Bool.and_eq_true] at hok
    have hx := h (i, z) (by simp)
    have hfit := fzOK_fit M i z o hok.1
    have hF := OutFrame.fzStep M 1 i z o 0
    have ho : (o + fzEv M z.e).toNat = o.toNat + (fzEv M z.e).toNat := toNat_add_lt _ _ (by omega)
    simp only [xsGo]
    rw [xsGo_keep xs _ _ (fun y hy => ⟨(h y (by simp [hy])).1, by have := (h y (by simp [hy])).2; omega⟩)
      hok.2 (by rw [hF.size]; exact hlt) k (by omega) (fun y hy => hne y (by simp [hy])),
      fzStep_low M i z o (by omega) hx.1 hok.1 hlt k hk (hne (i, z) (by simp)).1 (hne (i, z) (by simp)).2]

/-- **Each solution image's entry and words survive the later ones**, at an offset no lower than
the first and inside the buffer's length. -/
theorem xsGo_put : ∀ (xs : List (Nat × Fz)) (M : Mem) (o : Word),
    (xs.map (·.1)).Nodup → (∀ x ∈ xs, x.2.src ≠ OUT ∧ x.2.e.fzOk = true ∧ 12 + 2 * x.1 ≤ o.toNat) →
    xsOK xs M o = true → (M.arr64 OUT).size < 2 ^ 64 →
    ∀ x ∈ xs, ∃ ox : Word, o.toNat ≤ ox.toNat ∧
      ox.toNat + (fzEv M x.2.e).toNat ≤ (xsGo xs M o).2.toNat ∧
      (fzEv M x.2.e).toNat ≤ (M.arr64 x.2.src).size ∧
      ((xsGo xs M o).1.arr64 OUT).getD (10 + 2 * x.1) 0 = ox ∧
      ((xsGo xs M o).1.arr64 OUT).getD (11 + 2 * x.1) 0 = fzEv M x.2.e ∧
      ∀ t < (fzEv M x.2.e).toNat, ((xsGo xs M o).1.arr64 OUT).getD (ox.toNat + t) 0 = (M.arr64 x.2.src).getD t 0
  | [], _, _, _, _, _, _, _, hx => absurd hx (by simp)
  | (i, z) :: xs, M, o, hnd, h, hok, hlt, x, hx => by
    simp only [xsOK, Bool.and_eq_true] at hok
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hz := h (i, z) (by simp)
    have hfit := fzOK_fit M i z o hok.1
    have hF := OutFrame.fzStep M 1 i z o 0
    have ho : (o + fzEv M z.e).toNat = o.toNat + (fzEv M z.e).toNat := toNat_add_lt _ _ (by omega)
    have h' : ∀ y ∈ xs, y.2.src ≠ OUT ∧ y.2.e.fzOk = true ∧ 12 + 2 * y.1 ≤ (o + fzEv M z.e).toNat :=
      fun y hy => ⟨(h y (by simp [hy])).1, (h y (by simp [hy])).2.1, by have := (h y (by simp [hy])).2.2; omega⟩
    have hlt' : ((fzStep M 1 i z o 0).arr64 OUT).size < 2 ^ 64 := by rw [hF.size]; exact hlt
    obtain ⟨-, hX1, -, -⟩ := xsGo_low (o + fzEv M z.e).toNat xs (fzStep M 1 i z o 0) (o + fzEv M z.e)
      (fun y hy => ⟨(h' y hy).1, (h' y hy).2.2⟩) hok.2 hlt'
    simp only [xsGo]
    rcases List.mem_cons.mp hx with hxe | hx'
    · subst hxe
      dsimp only
      obtain ⟨p1, p2, p3⟩ := fzStep_put M i z o hz.1 hok.1 hlt hz.2.2
      have hparts := fzOK_parts M i z o hok.1
      refine ⟨o, Nat.le_refl _, by omega, hparts.2, ?_, ?_, fun t ht => ?_⟩
      · rw [xsGo_keep xs _ _ (fun y hy => ⟨(h' y hy).1, (h' y hy).2.2⟩) hok.2 hlt' _ (by omega)
          (fun y hy => by have : y.1 ≠ i := fun e => hnd.1 (List.mem_map.mpr ⟨y, hy, e⟩); omega), p1]
      · rw [xsGo_keep xs _ _ (fun y hy => ⟨(h' y hy).1, (h' y hy).2.2⟩) hok.2 hlt' _ (by omega)
          (fun y hy => by have : y.1 ≠ i := fun e => hnd.1 (List.mem_map.mpr ⟨y, hy, e⟩); omega), p2]
      · rw [xsGo_keep xs _ _ (fun y hy => ⟨(h' y hy).1, (h' y hy).2.2⟩) hok.2 hlt' _ (by omega)
          (fun y hy => by have := (h y (by simp [hy])).2.2; omega), p3 t ht]
    · obtain ⟨ox, q1, q2, q3, q4, q5, q6⟩ := xsGo_put xs _ _ hnd.2 h' hok.2 hlt' x hx'
      have hx2 := h x (by simp [hx'])
      have he := (fzEv_congr hF.arr _ hx2.2.1).1
      have hs := hF.arr _ (TieredArray.t0_ne hx2.1)
      simp only [he, hs] at q2 q3 q5 q6
      exact ⟨ox, by omega, q2, q3, q4, q5, q6⟩

/-! ### Header S's view -/

theorem xsL_facts : (xsL.map (·.1)).Nodup ∧ (∀ x ∈ xsL, x.2.src ≠ OUT ∧ x.2.e.fzOk = true ∧ 12 + 2 * x.1 ≤ hdrW) := by
  refine ⟨by decide, fun x hx => ?_⟩
  have := List.all_eq_true.mp xsL_ok x hx
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  refine ⟨this.2, this.1, ?_⟩
  simp only [xsL, fzsImgs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl <;> decide

theorem hsE_extra_iff {i : Nat} (hi : i < frozen.length) : hsE i = .extra ↔ i ∈ xsL.map (·.1) := by
  have : (List.range frozen.length).all (fun i => decide (hsE i = .extra) == (xsL.map (·.1)).contains i) = true := by
    decide +kernel
  have h := List.all_eq_true.mp this i (List.mem_range.mpr hi)
  simp only [beq_iff_eq] at h
  constructor
  · intro e; have := h; rw [decide_eq_true e] at this; exact List.contains_iff_mem.mp this.symm
  · intro hm; have hc := List.contains_iff_mem.mpr hm; rw [hc] at h; exact of_decide_eq_true h

section viewS
variable {m9 : Mem}

/-- **The words of header S's entries** in the final memory, for an entry made from header C's. -/
theorem cmpS_entry (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64)
    (hS : CmpHdrSOK (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) {i : Nat} (hi : i < frozen.length)
    (v : Word × Word) (hv : hsVal (parCompactMem m9 1 hdrWW) i = some v) :
    ((cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).arr64 OUT).getD (10 + 2 * i) 0 = v.1 ∧
    ((cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).arr64 OUT).getD (11 + 2 * i) 0 = v.2 := by
  obtain ⟨hsz, ho0, hlc, h256, hX1, hX2, h1, h5, hk⟩ := cmpC_facts hok hlt hS
  have hhw := hdrW_eq
  have hfl := frozen_length
  have hnex : hsE i ≠ .extra := by intro e; unfold hsVal at hv; rw [e] at hv; cases hv
  have hni : i ∉ xsL.map (·.1) := fun h => hnex ((hsE_extra_iff hi).mpr h)
  have hb : hdrWW.toNat + hdrW < 2 ^ 64 := by simp [hdrWW]; omega
  have hMs : ((parCompactMem m9 1 hdrWW).arr64 OUT).size = (m9.arr64 OUT).size :=
    (parCompactMem_out_b m9 1 hdrWW).size OUT
  have hW := parCompactOK_hdr_b hok hb
  obtain ⟨hM1s, -⟩ := hsMem_high (List.range frozen.length) (parCompactMem m9 1 hdrWW)
    (fun i hi => List.mem_range.mp hi)
  have hE := hsMem_entry (List.range frozen.length) (parCompactMem m9 1 hdrWW) List.nodup_range
    (fun i hi => List.mem_range.mp hi) (by rw [hMs]; simp [hdrWW] at hW; omega) i (List.mem_range.mpr hi) v hv
  have hkeep : ∀ k, k < (hdrW.toUInt64 + fzOff m9 frozen.length).toNat → (∀ x ∈ xsL, k ≠ 10 + 2 * x.1 ∧ k ≠ 11 + 2 * x.1) →
      ((hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1.arr64 OUT).getD k 0 =
      ((hsMem (parCompactMem m9 1 hdrWW) (List.range frozen.length)).arr64 OUT).getD k 0 := fun k hk hne =>
    xsGo_keep xsL _ _ (fun x hx => ⟨(xsL_facts.2 x hx).1, by have := (xsL_facts.2 x hx).2.2; omega⟩) hS.1
      (by rw [hM1s, hMs]; exact hlt) k hk hne
  have hne : ∀ k, (k = 10 + 2 * i ∨ k = 11 + 2 * i) → ∀ x ∈ xsL, k ≠ 10 + 2 * x.1 ∧ k ≠ 11 + 2 * x.1 := by
    intro k hk x hx
    have : x.1 ≠ i := fun e => hni (List.mem_map.mpr ⟨x, hx, e⟩)
    omega
  simp only [cmpHdrSMem]
  rw [hsTail_high _ _ _ (by omega), seedMem_low _ _ (by omega) _ (by omega), hkeep _ (by omega) (hne _ (.inl rfl)),
    hsTail_high _ _ _ (by omega), seedMem_low _ _ (by omega) _ (by omega), hkeep _ (by omega) (hne _ (.inr rfl))]
  exact hE

end viewS

theorem seedFold_at (so : Word) (hso : so.toNat + 256 < 2 ^ 64) : ∀ (ks : List Nat) (M : Mem),
    (∀ k ∈ ks, k < 256) → ks.Nodup → ∀ t, t < 256 →
    ((ks.foldl (seedPut so) M).arr64 OUT).getD (so.toNat + t) 0 =
      if t ∈ ks ∧ so.toNat + t < (M.arr64 OUT).size then rd64 M L.Checker.SCTL t.toUInt64
      else (M.arr64 OUT).getD (so.toNat + t) 0
  | [], _, _, _, _, _ => by simp
  | j :: ks, M, h, hnd, t, ht => by
    simp only [List.nodup_cons] at hnd
    have hj := h j (by simp)
    rw [List.foldl_cons, seedFold_at so hso ks _ (fun x hx => h x (by simp [hx])) hnd.2 t ht, seedPut,
      L.Mem.size64_set64, getD_set64_same, toNat_badd _ _ (by omega),
      rd64_set64_out _ L.Checker.SCTL (by decide)]
    by_cases htj : t = j
    · subst htj
      simp [hnd.1]
    · simp only [List.mem_cons, htj, false_or]
      (repeat' split) <;> first | rfl | omega

theorem seedMem_at (M : Mem) (so : Word) (hso : so.toNat + 256 ≤ (M.arr64 OUT).size)
    (hlt : (M.arr64 OUT).size < 2 ^ 64) (t : Nat) (ht : t < 256) :
    ((seedMem M so).arr64 OUT).getD (so.toNat + t) 0 =
      if t = 224 then 0 else if 162 ≤ t ∧ t ≤ 173 then rd64 M L.Checker.SCTL t.toUInt64
      else if t = 128 then rd64 M CTL (Nat.toUInt64 225) else (M.arr64 OUT).getD (so.toNat + t) 0 := by
  have hW : ∀ k ∈ hsSeedW, k < 256 := by decide
  have hWn : hsSeedW.Nodup := by decide
  have hWm : t ∈ hsSeedW ↔ 162 ≤ t ∧ t ≤ 173 := by
    simp only [hsSeedW, List.mem_map, List.mem_range]; constructor
    · rintro ⟨a, ha, rfl⟩; omega
    · intro h; exact ⟨t - 162, by omega, by omega⟩
  simp only [seedMem]
  rw [getD_set64_same, toNat_badd _ _ (by omega), seedFold_at so (by omega) hsSeedW _ hW hWn t ht,
    L.Mem.size64_set64, getD_set64_same, toNat_badd _ _ (by omega), (OutFrame.seedFold so hsSeedW _).size,
    L.Mem.size64_set64, rd64_set64_out _ L.Checker.SCTL (by decide)]
  by_cases h224 : t = 224
  · subst h224; simp; omega
  · rw [ite_eq_right (by omega), ite_eq_right h224]
    by_cases hs : 162 ≤ t ∧ t ≤ 173
    · rw [ite_eq_left ⟨hWm.mpr hs, by omega⟩, ite_eq_left hs]
    · rw [ite_eq_right (fun h => hs (hWm.mp h.1)), ite_eq_right hs]
      by_cases h128 : t = 128
      · subst h128; simp; omega
      · rw [ite_eq_right (by omega), ite_eq_right h128]

section viewS2
variable {m9 : Mem}

/-- **A solution image's entry and words** in the final memory (the seed's before its patches). -/
theorem cmpS_extra (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64)
    (hS : CmpHdrSOK (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)) (x : Nat × Fz) (hx : x ∈ xsL) :
    ∃ ox : Word, (hdrW.toUInt64 + fzOff m9 frozen.length).toNat ≤ ox.toNat ∧
      ox.toNat + (fzEv m9 x.2.e).toNat ≤ (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2.toNat ∧
      (fzEv m9 x.2.e).toNat ≤ (m9.arr64 x.2.src).size ∧
      ((cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).arr64 OUT).getD (10 + 2 * x.1) 0 = ox ∧
      ((cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).arr64 OUT).getD (11 + 2 * x.1) 0 =
        fzEv m9 x.2.e ∧
      ∀ t < (fzEv m9 x.2.e).toNat,
        ((hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1.arr64 OUT).getD (ox.toNat + t) 0 =
          (m9.arr64 x.2.src).getD t 0 := by
  obtain ⟨hsz, ho0, hlc, h256, hX1, hX2, h1, h5, hk⟩ := cmpC_facts hok hlt hS
  have hhw := hdrW_eq
  have hMs : ((parCompactMem m9 1 hdrWW).arr64 OUT).size = (m9.arr64 OUT).size :=
    (parCompactMem_out_b m9 1 hdrWW).size OUT
  have hF : OutFrame m9 (hsMem (parCompactMem m9 1 hdrWW) (List.range frozen.length)) :=
    (parCompactMem_out_b m9 1 hdrWW).trans (OutFrame.hsMem _ _)
  obtain ⟨ox, q1, q2, q3, q4, q5, q6⟩ := xsGo_put xsL _ _ xsL_facts.1
    (fun y hy => ⟨(xsL_facts.2 y hy).1, (xsL_facts.2 y hy).2.1, by have := (xsL_facts.2 y hy).2.2; omega⟩)
    hS.1 (by rw [hF.size]; exact hlt) x hx
  have hx2 := xsL_facts.2 x hx
  have he := (fzEv_congr hF.arr _ hx2.2.1).1
  have hs := hF.arr _ (TieredArray.t0_ne hx2.1)
  simp only [he, hs] at q2 q3 q5 q6
  refine ⟨ox, q1, q2, q3, ?_, ?_, fun t ht => ?_⟩
  · simp only [cmpHdrSMem]
    rw [hsTail_high _ _ _ (by omega), seedMem_low _ _ (by omega) _ (by have := hx2.2.2; omega)]
    exact q4
  · simp only [cmpHdrSMem]
    rw [hsTail_high _ _ _ (by omega), seedMem_low _ _ (by omega) _ (by have := hx2.2.2; omega)]
    exact q5
  · exact q6 t ht

theorem seedFold_high (so : Word) (hso : so.toNat + 256 < 2 ^ 64) : ∀ (ks : List Nat) (M : Mem),
    (∀ k ∈ ks, k < 256) → ∀ k, so.toNat + 256 ≤ k →
    ((ks.foldl (seedPut so) M).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0
  | [], _, _, _, _ => rfl
  | j :: ks, M, h, k, hk => by
    have hj := h j (by simp)
    rw [List.foldl_cons, seedFold_high so hso ks _ (fun x hx => h x (by simp [hx])) k hk, seedPut,
      getD_set64_ne _ _ _ _ _ (by rw [toNat_badd _ _ (by omega)]; omega)]

/-- The seed's patches leave every word from the seed's end on. -/
theorem seedMem_high (M : Mem) (so : Word) (hso : so.toNat + 256 < 2 ^ 64) (k : Nat) (hk : so.toNat + 256 ≤ k) :
    ((seedMem M so).arr64 OUT).getD k 0 = (M.arr64 OUT).getD k 0 := by
  have hW : ∀ k ∈ hsSeedW, k < 256 := by decide
  simp only [seedMem]
  rw [getD_set64_ne _ _ _ _ _ (by rw [toNat_badd _ _ (by omega)]; omega),
    seedFold_high so hso hsSeedW _ hW k hk,
    getD_set64_ne _ _ _ _ _ (by rw [toNat_badd _ _ (by omega)]; omega)]


/-- Header C's entry `j` read through `hsVal` (header C at `OUT[hdrW‥)`): its offset (relative to
header C) and its extent. -/
theorem hsVal_C (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64) {j : Nat}
    (hj : j < frozen.length) :
    rd64 (parCompactMem m9 1 hdrWW) OUT (hdrW + (10 + 2 * j)).toUInt64 = fzOff m9 j ∧
    rd64 (parCompactMem m9 1 hdrWW) OUT (hdrW + (11 + 2 * j)).toUInt64 = UInt64.ofNat (fzExt m9 (fzAt j)) := by
  have hhw := hdrW_eq
  have hfl := frozen_length
  have hb : hdrWW.toNat + hdrW < 2 ^ 64 := by simp [hdrWW]; omega
  have hb' : hdrWW.toNat = hdrW := by simp [hdrWW]; omega
  have := parCompactMem_entry_b hok hb (fun _ => hlt) hj
  rw [hb'] at this
  simp only [rd64]
  rw [toNat_c _ (by omega), toNat_c _ (by omega)]
  exact this

theorem viewSArr_s (m : Mem) : viewSArr m ↑L.Front.DECL = m.arr64 L.Checker.SDECL ∧
    viewSArr m ↑FIRSTS = m.arr64 L.Checker.SFIRSTS ∧ viewSArr m ↑L.Front.DLP = m.arr64 L.Checker.SDLP := by
  unfold viewSArr
  refine ⟨?_, ?_, ?_⟩
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_left rfl]
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]
  · rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
      ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_left rfl]

/-- **The solution's own images**: `viewS` shows its records, firsts and declaration pool where
header S's entries point. -/
theorem fzEv_cmpOr (M : Mem) (h : fzEv M (fzCtl cmpCW) = 1) (e : Expr) (k : Nat) :
    fzEv M (fzCmpOr e k) = fzEv M (fzCtl k) := by
  simp only [fzCmpOr, fzEv_bin, h, BinOp.eval, UInt64.one_mul]; grind

theorem extra_view (m : Mem) (hcw : fzEv m (fzCtl cmpCW) = 1) (x : Nat × Fz) (hx : x ∈ fzsImgs) :
    (viewS m).arr64 (fzAt x.1).src = m.arr64 x.2.src ∧ fzEv (viewS m) (fzAt x.1).e = fzEv m x.2.e := by
  have hv := viewSArr_s m
  have hcw' : fzEv (viewS m) (fzCtl cmpCW) = 1 := by
    rw [fzEv_ctl_viewS m cmpCW (by decide) (by decide)]; exact hcw
  have hD := fzEv_ctl_viewS m cmpKD (by decide) (by decide)
  have hP := fzEv_ctl_viewS m cmpKP (by decide) (by decide)
  simp only [fzsImgs, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · refine ⟨?_, ?_⟩
    · show viewSArr m ↑FIRSTS = _; exact hv.2.1
    · show fzEv (viewS m) (fzCmpOr fzDecl cmpKD) = fzEv m (fzCtl cmpKD)
      rw [fzEv_cmpOr _ hcw', hD]
  · refine ⟨?_, ?_⟩
    · show viewSArr m ↑L.Front.DECL = _; exact hv.1
    · show fzEv (viewS m) (.bin .add (fzC 1) (.bin .mul (fzC 8) (fzCmpOr fzDecl cmpKD))) =
        fzEv m (.bin .add (fzC 1) (.bin .mul (fzC 8) (fzCtl cmpKD)))
      simp only [fzEv_bin, fzEv_cmpOr _ hcw', hD]; rfl
  · refine ⟨?_, ?_⟩
    · show viewSArr m ↑L.Front.DLP = _; exact hv.2.2
    · show fzEv (viewS m) (.bin .add (fzC 1) (fzCmpOr (.ld64 L.Front.DLP (fzC 0)) cmpKP)) =
        fzEv m (.bin .add (fzC 1) (fzCtl cmpKP))
      simp only [fzEv_bin, fzEv_cmpOr _ hcw', hP]; rfl

/-- Header C's images, moved to header S's offsets, lie below the solution's images. -/
theorem cmpS_offs (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64) {j : Nat}
    (hj : j < frozen.length) :
    (fzOff m9 j + hdrW.toUInt64).toNat = hdrW + (fzOff m9 j).toNat ∧
    hdrW + (fzOff m9 j).toNat + fzExt m9 (fzAt j) ≤ (hdrW.toUInt64 + fzOff m9 frozen.length).toNat := by
  have hhw := hdrW_eq
  have hfl := frozen_length
  have hb : hdrWW.toNat + hdrW < 2 ^ 64 := by simp [hdrWW]; omega
  have hW := parCompactOK_hdr_b hok hb
  have hg : (∀ j ≤ frozen.length, (fzOff m9 j).toNat = hdrW + fzSum m9 j) ∧
      hdrWW.toNat + hdrW + fzSum m9 frozen.length ≤ (m9.arr64 OUT).size := by
    have h' := hok
    simp only [parCompactOK, Bool.and_eq_true] at h'
    exact (pcGo_good m9 1 hdrWW hW hb (fun _ => hlt) frozen.length (Nat.le_refl _) h'.1.1.1).1 one_ne_zero'
  have hb' : hdrWW.toNat = hdrW := by simp [hdrWW]; omega
  have h1 := hg.1 j (by omega)
  have h2 := hg.1 _ (Nat.le_refl _)
  have hm := fzSum_mono m9 (j := j + 1) (n := frozen.length) (by omega)
  rw [fzSum_succ, ← fzExt_eq] at hm
  refine ⟨?_, ?_⟩
  · rw [UInt64.toNat_add, toNat_c _ (by omega), Nat.mod_eq_of_lt (by omega)]; omega
  · rw [UInt64.toNat_add, toNat_c _ (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- **Header S's view**: the whole buffer shows the solution's phase `viewS m9` (the challenge's
index state with the solution's index rows, records, firsts, declaration pool and seed words), and
names header C as the next phase (word `5`). -/
theorem cmpView_S (hok : parCompactOK m9 1 hdrWW = true) (hlt : (m9.arr64 OUT).size < 2 ^ 64)
    (hS : CmpHdrSOK (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))
    (h224 : rd64 m9 CTL (Nat.toUInt64 cmpCW) = 1) :
    HdrView (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))) (viewS m9) ∧
    (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).getD 5 0 = hdrWW := by
  obtain ⟨hsz, ho0, hlc, h256, hX1, hX2, h1, h5, hk⟩ := cmpC_facts hok hlt hS
  have hhw := hdrW_eq
  have hSz : (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).size =
      (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2.toNat := by
    simp only [cmpBufS, h1, Array.size_extract]; omega
  have hSg : ∀ k < (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2.toNat,
      (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).getD k 0 =
      ((cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).arr64 OUT).getD k 0 := by
    intro k hk'
    simp only [cmpBufS, h1]
    rw [getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add]
  refine ⟨⟨fun i hi => ?_, fun i hi => ?_, ?_, ?_, fun i hi => ?_⟩, by rw [hSg 5 (by omega), h5]⟩
  · sorry -- img: by hsE i (same: cmpS_entry + parCompactMem_img_b + same_view; zero: zero_view; extra:
          -- cmpS_extra + seedMem_at (entry 0) / seedMem_high (60‥62) + viewSArr)
  · obtain ⟨_, -, -, hc256, -⟩ := cmpS_extra hok hlt hS (0, fzAt 0) (by simp [xsL])
    have hctl : 256 ≤ (m9.arr64 CTL).size := by
      have e : fzEv m9 (fzAt 0).e = 256 := rfl
      have e2 : (fzAt 0).src = CTL := rfl
      rw [e, e2] at hc256; simpa using hc256
    cases hE : hsE i with
    | same j =>
      obtain ⟨v1, v2⟩ := same_view m9 h224 hi hE
      rw [fzExt_eq, v1, v2, ← fzExt_eq]
      exact fzExt_le_src (b := hdrWW) hok (hsE_lt hi j hE)
    | extra =>
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hsE_extra_iff hi).mp hE)
      simp only [xsL, List.mem_cons] at hx
      rcases hx with rfl | hx'
      · show fzExt (viewS m9) (fzAt 0) ≤ ((viewS m9).arr64 ↑CTL).size
        rw [viewS_ctl]
        have hs' : (viewSCtl m9).size = (m9.arr64 CTL).size := by
          have hfs : ∀ (ks : List Nat) (c : Array Word),
              (ks.foldl (fun c k => c.setIfInBounds k ((m9.arr64 L.Checker.SCTL).getD k 0)) c).size = c.size := by
            intro ks; induction ks with
            | nil => intro c; rfl
            | cons k ks ih => intro c; rw [List.foldl_cons, ih, Array.size_setIfInBounds]
          unfold viewSCtl
          rw [Array.size_setIfInBounds, hfs, Array.size_setIfInBounds]
        rw [hs']
        exact hctl
      · obtain ⟨_, -, -, q3, -⟩ := cmpS_extra hok hlt hS x (by simp [xsL, hx'])
        obtain ⟨w1, w2⟩ := extra_view m9 h224 x hx'
        rw [fzExt_eq, w1, w2]
        exact q3
  · have h9 : 9 < ((seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
        (hdrW.toUInt64 + fzOff m9 frozen.length)).arr64 OUT).size := by
      have e := hsTail_size (seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
        (hdrW.toUInt64 + fzOff m9 frozen.length)) (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2
      simp only [cmpHdrSMem] at hsz
      omega
    have hT := hsTail_words _ (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2 h9
    simp only [bufEntry, Nat.mul_zero, Nat.add_zero]
    rw [hSg 8 (by omega), hSg 9 (by omega)]
    simp only [cmpHdrSMem]
    rw [hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2]
    simp [hdrWW, hhw]
  · have h9 : 9 < ((seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
        (hdrW.toUInt64 + fzOff m9 frozen.length)).arr64 OUT).size := by
      have e := hsTail_size (seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
        (hdrW.toUInt64 + fzOff m9 frozen.length)) (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2
      simp only [cmpHdrSMem] at hsz
      omega
    have hT := hsTail_words _ (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2 h9
    have hFr : OutFrame m9 (seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
        (hdrW.toUInt64 + fzOff m9 frozen.length)) :=
      (((parCompactMem_out_b m9 1 hdrWW).trans (OutFrame.hsMem _ _)).trans (OutFrame.xsGo _ _ _)).trans
        (((OutFrame.set64 _ _ _).trans (OutFrame.seedFold _ _ _)).trans (OutFrame.set64 _ _ _))
    obtain ⟨_, -, -, hc256, -⟩ := cmpS_extra hok hlt hS (0, fzAt 0) (by simp [xsL])
    have hctl : 256 ≤ (m9.arr64 CTL).size := by
      have e : fzEv m9 (fzAt 0).e = 256 := rfl
      have e2 : (fzAt 0).src = CTL := rfl
      rw [e, e2] at hc256; simpa using hc256
    have hb0 : bufImg (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))) 0 =
        (cmpBufS OUT (cmpHdrSMem (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length))).extract 0 hdrW := by
      simp only [bufImg, bufEntry, Nat.mul_zero, Nat.add_zero]
      rw [hSg 8 (by omega), hSg 9 (by omega)]
      simp only [cmpHdrSMem]
      rw [hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2]
      simp [hdrWW, hhw]
    have hvd : viewSArr m9 ↑L.Front.DECL = m9.arr64 L.Checker.SDECL := by
      unfold viewSArr
      rw [ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide), ite_eq_right (by decide),
        ite_eq_right (by decide), ite_eq_left rfl]
    rw [hb0, getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add,
      getD_extract_lt _ _ _ _ (by simp only [Array.size_extract]; omega), Nat.zero_add,
      hSg 2 (by omega), hSg 3 (by omega)]
    simp only [cmpHdrSMem]
    rw [hT.2.2.1, hT.2.2.2.1]
    refine ⟨?_, ?_⟩
    · have hv : (viewS m9).arr64 ↑L.Front.DECL = m9.arr64 L.Checker.SDECL := by
        simp only [viewS, Mem.arr64]; exact hvd
      simp only [rd64, hFr.arr (L.Checker.SDECL : TieredArray) (by decide), hv]
    · simp only [rd64, hFr.arr (CTL : TieredArray) (by decide), viewS_ctl]
      have e1 : UInt64.toNat 128 = (Nat.toUInt64 128).toNat := rfl
      have e2 : UInt64.toNat 225 = 225 := rfl
      rw [e1, viewSCtl_128 m9 (by omega), e2]
  · have hfl := frozen_length
    rw [hSz]
    rcases i with _ | i
    · simp only [bufEntry, Nat.mul_zero, Nat.add_zero]
      rw [hSg 8 (by omega), hSg 9 (by omega)]
      have h9 : 9 < ((seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
          (hdrW.toUInt64 + fzOff m9 frozen.length)).arr64 OUT).size := by
        have e := hsTail_size (seedMem (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).1
          (hdrW.toUInt64 + fzOff m9 frozen.length)) (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2
        simp only [cmpHdrSMem] at hsz
        omega
      have hT := hsTail_words _ (hsImgs (parCompactMem m9 1 hdrWW) (fzOff m9 frozen.length)).2 h9
      simp only [cmpHdrSMem]
      rw [hT.2.2.2.2.2.2.1, hT.2.2.2.2.2.2.2]
      have e154 : hdrWW.toNat = 154 := rfl
      have e0 : (0 : Word).toNat = 0 := rfl
      rw [e154, e0]
      have := hX1
      omega
    · have hi' : i < frozen.length := by have := frozenIdsL_length; omega
      simp only [bufEntry, show 8 + 2 * (i + 1) = 10 + 2 * i by omega, show 9 + 2 * (i + 1) = 11 + 2 * i by omega]
      rw [hSg _ (by omega), hSg _ (by omega)]
      cases hE : hsE i with
      | same j =>
        have hj := hsE_lt hi' j hE
        have hv : hsVal (parCompactMem m9 1 hdrWW) i = some (rd64 (parCompactMem m9 1 hdrWW) OUT
            (hdrW + (10 + 2 * j)).toUInt64 + hdrW.toUInt64, rd64 (parCompactMem m9 1 hdrWW) OUT
            (hdrW + (11 + 2 * j)).toUInt64) := by simp only [hsVal, hE]
        obtain ⟨e1, e2⟩ := cmpS_entry hok hlt hS hi' _ hv
        obtain ⟨c1, c2⟩ := hsVal_C hok hlt hj
        rw [e1, e2, c1, c2]
        obtain ⟨o1, o2⟩ := cmpS_offs hok hlt hj
        rw [o1, UInt64.toNat_ofNat_of_lt' (by rw [fzExt_eq]; exact UInt64.toNat_lt_size _)]
        omega
      | extra =>
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ((hsE_extra_iff hi').mp hE)
        obtain ⟨ox, -, q2, -, q4, q5, -⟩ := cmpS_extra hok hlt hS x hx
        rw [q4, q5]
        exact q2

end viewS2

end L.Arena
