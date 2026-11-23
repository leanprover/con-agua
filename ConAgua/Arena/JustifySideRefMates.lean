module

public import ConAgua.Arena.JustifySideRefSide
public import ConAgua.Arena.JustifySideRefMove
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.JustifySideModels
import all ConAgua.Arena.JustifyIface
import ConAgua.Arena.DeclAndPinInd

@[expose] public section

/-!
# The record mates: the refinements (lane compare)

`solution_of(cnt)` refines `recordMatesGo ∅` over the front's records (`solutionOf`'s mates):
after it the rows `MAT*` hold the twin's map (`MatesR`), each list a tier-0 `EREC` slice. With
`index_to_solution` (`SolIdxR`) this is `SolR` of `solutionOf`.
-/

set_option experimental.vcgen true
set_option linter.unusedSimpArgs false
set_option autoImplicit false

open Std.WP
open scoped Lean.Order
open ConRon.Arena

namespace L.Arena

open L.Front (DECL DLP DeclsF DeclAtF DeclAt CVAt dw decCIs trunc IndDeclAt)

/-! ## `mates_set` -/

/-- `mates_set(w, o, l)`'s memory: the row of `w` in its tag's array. -/
def matSetM (m : Mem) (w o l : Word) : Mem :=
  (m.set64 (matArr (rowTag w)) (idxW w <<< 1) o).set64 (matArr (rowTag w)) ((idxW w <<< 1) + 1) l

theorem matesSet_spec (p : Prog) (hp : p.lookup "mates_set" = some matesSetL) (n : Nat) (s₀ : St)
    (w o l : Word) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "mates_set" [w, o, l]
    ⦃fun _ s' => LocEq s' s₀ ∧ rowTier w = 0 ∧ rowTag w ≤ 2 ∧ s'.mem = matSetM s₀.mem w o l ∧
      rowIx w + 1 < (s₀.mem.arr64 (matArr (rowTag w))).size; ⊤⦄ := by
  rw [invoke_eq _ hp]
  simp only [callFn, matesSetL]
  cases n with
  | zero => vcgen [exec] <;> grind
  | succ n =>
    vcgen [exec, step, L.evalC_spec, L.evalE_spec, evalArgs, setLoc, setLocs, st64]
    all_goals simp only [Cond.pval, Expr.pval, Expr.pval_tagE, Expr.pval_tierE, Expr.pval_idxE,
      St.setLoc_loc, L.St.setLoc_mem, Locals.init_cons_zero, Cmp.eval, BinOp.eval, rd64_rdWC,
      beq_iff_eq, bne_iff_ne, ne_eq] at *
    all_goals subst_vars
    all_goals simp_all [LocEq, Sig.retVal, Sig.retOr, matSetM, matArr, rowTag_of, rowTier_of,
      Locals.init_cons_succ, Locals.init_cons_zero, MATA, MATS, MATN, rowIx, Mem.size_arr64_set64]
    all_goals (try rfl)
    all_goals (have := UInt64.lt_iff_toNat_lt.mp (idxW_lt w); simp [Nat.shiftLeft_eq] at *; omega)

theorem matArr_inj {g g' : Nat} (h : g ≤ 2) (h' : g' ≤ 2) (e : (matArr g : TieredArray) = matArr g') :
    g = g' := by
  unfold matArr at e
  rcases (by omega : g = 0 ∨ g = 1 ∨ g = 2) with a | a | a <;>
  rcases (by omega : g' = 0 ∨ g' = 1 ∨ g' = 2) with b | b | b <;> simp [a, b, MATA, MATS, MATN] at e <;> omega

/-- **The row after `mates_set`**: the rows of `w`'s tag and index are the new words, every other
row kept. -/
theorem matRow_matSet {m : Mem} {w o l : Word} (x : Word) (ht : rowTag w ≤ 2) (_h0 : rowTier w = 0)
    (hb : rowIx w + 1 < (m.arr64 (matArr (rowTag w))).size) :
    matRow (matSetM m w o l) x = if rowTag x ≤ 2 ∧ rowTier x = 0 ∧ rowTag x = rowTag w ∧
      rowIx x = rowIx w then (o, l) else matRow m x := by
  have e1 : (idxW w <<< 1).toNat = rowIx w := ixW_toNat w
  have e2 : ((idxW w <<< 1) + 1).toNat = rowIx w + 1 := ixW_succ w
  have ev := rowIx_even x; have ev' := rowIx_even w
  unfold matRow
  by_cases hx : rowTag x ≤ 2 ∧ rowTier x = 0
  · simp only [hx, and_self, ite_true, true_and]
    simp only [matSetM, rdN_set64, size_set64_any, e1, e2]
    by_cases hs : rowTag x = rowTag w ∧ rowIx x = rowIx w
    · rw [ite_eq_left hs]; rw [hs.1, hs.2]
      simp [show rowIx w + 1 ≠ rowIx w by omega, hb, Nat.lt_of_succ_lt hb, Mem.size_arr64_set64]
    · rw [ite_eq_right hs]
      by_cases ha : (matArr (rowTag x) : TieredArray) = matArr (rowTag w)
      · have hg := matArr_inj hx.1 ht ha
        have hi : rowIx x ≠ rowIx w := fun e => hs ⟨hg, e⟩
        simp only [ha]
        simp [show rowIx w ≠ rowIx x by omega, show rowIx w + 1 ≠ rowIx x by omega,
          show rowIx w ≠ rowIx x + 1 by omega, show rowIx w + 1 ≠ rowIx x + 1 by omega]
      · simp [ha]
  · simp only [hx, ite_false]
    rw [ite_eq_right (fun c => hx ⟨c.1, c.2.1⟩)]

/-! ## The mates in L -/

/-- **The record mates' rows hold the map `M`**: every name's list is its row's slice, and every
non-empty row is a decoded slice below the record pool's tier-0 top. -/
structure MatesR (m : Mem) (M : Std.HashMap NIdx (List NIdx)) : Prop where
  get : ∀ n : NIdx, M[n]? = matList m n.word.toUInt64
  ok : ∀ w, (matRow m w).1 ≠ 0 →
    (matRow m w).1.toNat - 1 + (matRow m w).2.toNat ≤ erTop m ∧ (matList m w).isSome
  /-- An empty row has length `0`. -/
  z : ∀ w, (matRow m w).1 = 0 → (matRow m w).2 = 0

/-- Zero rows hold the empty map. -/
theorem MatesR.zero {m : Mem} (hz : ∀ g ≤ 2, ∀ j, rdN (m.arr64 (matArr g)) j = 0) : MatesR m ∅ := by
  have h0 : ∀ w, (matRow m w).1 = 0 ∧ (matRow m w).2 = 0 := fun w => by
    unfold matRow; split
    · rename_i h; exact ⟨hz _ h.1 _, hz _ h.1 _⟩
    · exact ⟨rfl, rfl⟩
  exact ⟨fun n => by simp [matList, (h0 _).1], fun w hw => absurd (h0 w).1 hw, fun w _ => (h0 w).2⟩

/-- `MatesR` across a growth of the record pool that keeps the rows. -/
theorem MatesR.grow {m m' : Mem} {M : Std.HashMap NIdx (List NIdx)} (h : MatesR m M)
    (hr : ∀ w, matRow m' w = matRow m w) (hg : ErecGrow m m') : MatesR m' M := by
  have hx := hg.ext
  have hl : ∀ w, matList m' w = matList m w := fun w => by
    unfold matList; rw [hr]
    split
    · rfl
    · rename_i c
      obtain ⟨xs, hxs⟩ := Option.isSome_iff_exists.mp (h.ok w c).2
      unfold matList at hxs; simp only [c, ite_false] at hxs
      rw [hxs, hx.hslice? hxs]
  refine ⟨fun n => by rw [h.get n, hl], fun w hw => ?_, fun w hw => by rw [hr] at hw ⊢; exact h.z w hw⟩
  rw [hr] at hw ⊢; rw [hl]
  exact ⟨Nat.le_trans (h.ok w hw).1 hg.top, (h.ok w hw).2⟩

/-- **One member's row written** (`mates_set(b, d + 1, k)`), its slice `(d, k)` decoding to `xs`
below the top. -/
theorem MatesR.set {m : Mem} {M : Std.HashMap NIdx (List NIdx)} (h : MatesR m M) {b d k : Word}
    (hb32 : b.toNat < 2 ^ 32) (ht : rowTag b ≤ 2) (h0 : rowTier b = 0)
    (hbd : rowIx b + 1 < (m.arr64 (matArr (rowTag b))).size)
    (hd : d.toNat + 1 < 2 ^ 64) {xs : List NIdx} (hs : hslice? (erecP m) d.toNat k.toNat = some xs)
    (htop : d.toNat + k.toNat ≤ erTop m) :
    MatesR (matSetM m b (d + 1) k) (M.insert (decI b) xs) := by
  have hP : erecP (matSetM m b (d + 1) k) = erecP m := by
    have ha : ∀ g, (matArr g : TieredArray) ≠ EREC ∧ (matArr g : TieredArray) ≠ tier1 EREC ∧
        (matArr g : TieredArray) ≠ CTL := fun g => by
      unfold matArr; split <;> (try split) <;> decide
    apply erecP_congr'
    · simp only [matSetM]; rw [Mem.arr64_set64_ne _ _ _ _ _ (ha _).1.symm, Mem.arr64_set64_ne _ _ _ _ _ (ha _).1.symm]
    · simp only [matSetM]; rw [Mem.arr64_set64_ne _ _ _ _ _ (ha _).2.1.symm, Mem.arr64_set64_ne _ _ _ _ _ (ha _).2.1.symm]
    · simp only [matSetM]; rw [Mem.arr64_set64_ne _ _ _ _ _ (ha _).2.2.symm, Mem.arr64_set64_ne _ _ _ _ _ (ha _).2.2.symm]
    · simp only [matSetM]; rw [Mem.arr64_set64_ne _ _ _ _ _ (ha _).2.2.symm, Mem.arr64_set64_ne _ _ _ _ _ (ha _).2.2.symm]
  have htp : erTop (matSetM m b (d + 1) k) = erTop m := by
    simp only [erTop]; congr 2
    have : (matArr (rowTag b) : TieredArray) ≠ CTL := by unfold matArr; split <;> (try split) <;> decide
    simp only [matSetM]; rw [Mem.arr64_set64_ne _ _ _ _ _ this.symm, Mem.arr64_set64_ne _ _ _ _ _ this.symm]
  have hd1 : (d + 1).toNat = d.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have hne : d + 1 ≠ 0 := fun e => by have := congrArg UInt64.toNat e; rw [hd1] at this; simp at this
  have hnew : matList (matSetM m b (d + 1) k) b = some xs := by
    unfold matList; rw [matRow_matSet b ht h0 hbd]; simp [ht, h0, hne, hP, hd1, hs]
  have hrow : ∀ x, ¬ (rowTag x ≤ 2 ∧ rowTier x = 0 ∧ rowTag x = rowTag b ∧ rowIx x = rowIx b) →
      matList (matSetM m b (d + 1) k) x = matList m x := fun x hx => by
    unfold matList; rw [matRow_matSet x ht h0 hbd, ite_eq_right hx, hP]
  refine ⟨fun n => ?_, fun w hw => ?_, fun w hw => ?_⟩
  · rw [Std.HashMap.getElem?_insert]
    by_cases e : n.word.toUInt64 = b
    · have : (decI b : NIdx) = n := by rw [← e]; exact decI_word n
      simp only [this, beq_self_eq_true, ite_true, e, hnew]
    · have hnb : (decI b == n) = false := by
        rw [nidx_beq, decI_word_self _ hb32]; simp [e]
      rw [hnb]; simp only [Bool.false_eq_true, ite_false]
      rw [h.get n, hrow]
      rintro ⟨t1, t2, t3, t4⟩
      exact e (row_inj (idx_word_lt32 n) hb32 t1 ht t3 (by rw [t2, h0]) t4)
  · rw [matRow_matSet w ht h0 hbd] at hw ⊢
    by_cases hs : rowTag w ≤ 2 ∧ rowTier w = 0 ∧ rowTag w = rowTag b ∧ rowIx w = rowIx b
    · rw [ite_eq_left hs] at hw ⊢
      have : matList (matSetM m b (d + 1) k) w = matList (matSetM m b (d + 1) k) b := by
        unfold matList; rw [matRow_matSet w ht h0 hbd, matRow_matSet b ht h0 hbd, ite_eq_left hs]
        simp [ht, h0]
      rw [this, hnew]; refine ⟨?_, rfl⟩; dsimp only; rw [htp, hd1]; omega
    · rw [ite_eq_right hs] at hw ⊢
      rw [hrow w hs, htp]; exact h.ok w hw
  · rw [matRow_matSet w ht h0 hbd] at hw ⊢
    by_cases hs : rowTag w ≤ 2 ∧ rowTier w = 0 ∧ rowTag w = rowTag b ∧ rowIx w = rowIx b
    · rw [ite_eq_left hs] at hw; exact absurd hw hne
    · rw [ite_eq_right hs] at hw ⊢; exact h.z w hw

/-! ## The copies -/

/-- What a copy loop has done up to `i`: `EREC[d‥d + i)` written by `v`, the rest of `EREC` and
every other array kept. -/
structure CpInv (m₀ m : Mem) (d : Nat) (v : Nat → Word) (i : Nat) : Prop where
  other : ∀ b, b ≠ (EREC : TieredArray) → m.arr64 b = m₀.arr64 b
  size : (m.arr64 EREC).size = (m₀.arr64 EREC).size
  out : ∀ x, (x < d ∨ d + i ≤ x) → rdN (m.arr64 EREC) x = rdN (m₀.arr64 EREC) x
  done : ∀ j < i, rdN (m.arr64 EREC) (d + j) = v j

theorem CpInv.start (m : Mem) (d : Nat) (v : Nat → Word) : CpInv m m d v 0 :=
  ⟨fun _ _ => rfl, rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem CpInv.step {m₀ m : Mem} {d : Nat} {v : Nat → Word} {i : Nat} (h : CpInv m₀ m d v i)
    {dw iw : Word} (_hd : dw.toNat = d) (_hi : iw.toNat = i) (hb : d + i < (m₀.arr64 EREC).size)
    (hdi : (dw + iw).toNat = d + i) {x : Word} (hx : x = v i) :
    CpInv m₀ (m.set64 EREC (dw + iw) x) d v (i + 1) := by
  refine ⟨fun b hb' => by rw [Mem.arr64_set64_ne _ _ _ _ _ hb']; exact h.other b hb',
    by rw [Mem.size_arr64_set64]; exact h.size, fun y hy => ?_, fun j hj => ?_⟩
  · rw [rdN_set64, hdi, ite_eq_right (by omega)]; exact h.out y (by omega)
  · rw [rdN_set64, hdi]
    by_cases e : j = i
    · subst e; rw [ite_eq_left ⟨rfl, rfl, by rw [h.size]; exact hb⟩, hx]
    · rw [ite_eq_right (by omega)]; exact h.done j (by omega)

theorem copyPrev_ok {m₀ : Mem} {d s l : Word} (hdl : d.toNat + l.toNat ≤ (m₀.arr64 EREC).size)
    (hsz : (m₀.arr64 EREC).size < 2 ^ 64) (hsl : s.toNat + l.toNat ≤ d.toNat) :
    ∀ n (m : Mem) (i : Word) (m' : Mem),
      CpInv m₀ m d.toNat (fun j => rdN (m₀.arr64 EREC) (s.toNat + j)) i.toNat → i ≤ l →
      sdCopyPrevW.loop1 n m d s l i = some m' →
      CpInv m₀ m' d.toNat (fun j => rdN (m₀.arr64 EREC) (s.toNat + j)) l.toNat := by
  intro n
  induction n with
  | zero => intro m i m' _ _ h; rw [sdCopyPrevW.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro m i m' hI hle h
    rw [sdCopyPrevW.loop1.eq_2] at h
    have hl64 := UInt64.toNat_lt l
    by_cases g : i < l
    · rw [ite_eq_left g] at h
      have gi := UInt64.lt_iff_toNat_lt.mp g
      have e1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hdi : (d + i).toNat = d.toNat + i.toNat := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hsi : (s + i).toNat = s.toNat + i.toNat := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      simp only [tierA_zero] at h
      have hx : rdW (m.arr64 EREC) (s + i) = rdN (m₀.arr64 EREC) (s.toNat + i.toNat) := by
        rw [rdW_rdN, hsi]; exact hI.out _ (.inl (by omega))
      exact ih _ _ _ (by rw [e1]; exact hI.step rfl rfl (by omega) hdi hx)
        (UInt64.le_iff_toNat_le.mpr (by rw [e1]; omega)) h
    · rw [ite_eq_right g] at h; cases h
      have : i = l := UInt64.le_antisymm hle (UInt64.not_lt.mp g)
      subst this; exact hI

/-- The name word `sd_copy_names` copies for member `j` of the block at `bo`. -/
def nameW (m : Mem) (bo j : Word) : Word :=
  rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (bo + j) + (CI.cv + CV.name)) &&& 4294967295

theorem copyNames_ok {m₀ : Mem} {d bo bl : Word} (hdl : d.toNat + bl.toNat ≤ (m₀.arr64 EREC).size)
    (hsz : (m₀.arr64 EREC).size < 2 ^ 64) :
    ∀ n (m : Mem) (j : Word) (m' : Mem),
      CpInv m₀ m d.toNat (fun i => nameW m₀ bo (UInt64.ofNat i)) j.toNat → j ≤ bl →
      sdCopyNamesW.loop1 n m d bo bl j = some m' →
      CpInv m₀ m' d.toNat (fun i => nameW m₀ bo (UInt64.ofNat i)) bl.toNat := by
  intro n
  induction n with
  | zero => intro m i m' _ _ h; rw [sdCopyNamesW.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro m i m' hI hle h
    have hl64 := UInt64.toNat_lt bl
    by_cases g : i < bl
    · rw [sdCopyNamesW.loop1.arm1 _ _ _ _ _ _ g] at h
      have gi := UInt64.lt_iff_toNat_lt.mp g
      have e1 : (i + 1).toNat = i.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      have hdi : (d + i).toNat = d.toNat + i.toNat := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
      have hP : m.arr64 DLP = m₀.arr64 DLP := hI.other _ (by decide)
      simp only [tierA_zero] at h
      have hx : rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (bo + i) + (CI.cv + CV.name)) &&& 4294967295 =
          nameW m₀ bo (UInt64.ofNat i.toNat) := by simp only [nameW, hP, UInt64.ofNat_toNat]
      exact ih _ _ _ (by rw [e1]; exact hI.step rfl rfl (by omega) hdi hx)
        (UInt64.le_iff_toNat_le.mpr (by rw [e1]; omega)) h
    · have : ¬ i < bl := g
      rw [sdCopyNamesW.loop1.eq_2, ite_eq_right this] at h; cases h
      have : i = bl := UInt64.le_antisymm hle (UInt64.not_lt.mp g)
      subst this; exact hI

/-! ## A block's names in `DLP` -/

/-- Member `j`'s name word of the block at `bo` (record pointers into the pool `P`). -/
def nmP (P : Array Word) (bo j : Nat) : Word := rdN P ((rdN P (bo + j)).toNat + CI.cv.toNat)

theorem block_names_dec {P : Array Word} {t : Nat} : ∀ (k bo : Nat) (block : List IConstantInfo),
    decCIs (trunc P t) bo k = some block → 0 < bo → (∀ j < k, rdN P (bo + j) ≠ 0) →
    block.length = k ∧ ∀ j (hj : j < k), ∃ h : j < block.length,
      (decI (nmP P bo j) : NIdx) = block[j].name ∧ (nmP P bo j).toNat < 2 ^ 32 ∧
      (rdN P (bo + j)).toNat + CI.cv.toNat < P.size ∧ bo + j < P.size := by
  intro k
  induction k with
  | zero => intro bo block h _ _; rw [L.Arena.decCIs_zero] at h; cases h; simp
  | succ k ih =>
    intro bo block h hbo hp
    rw [L.Arena.decCIs_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c, ⟨v, hv, hc⟩, cs, hcs, rfl⟩ := h
    obtain ⟨hl, hall⟩ := ih (bo + 1) cs hcs (by omega) (fun j hj => by
      have := hp (j + 1) (by omega); rwa [show bo + (j + 1) = bo + 1 + j by omega] at this)
    obtain ⟨w0, hw0, rfl⟩ : ∃ w, (trunc P t)[bo]? = some w ∧ w.toNat = v := by
      simpa [nat?, aread_apply] using hv
    obtain ⟨hP0, -⟩ := trunc_get_some hw0 (by omega)
    obtain ⟨w, hw, hw32, hname⟩ := decCI_name hc
    have hr0 : rdN P bo = w0 := by simp [rdN, hP0]
    have hne : w0 ≠ 0 := by have := hp 0 (by omega); simpa [hr0] using this
    have hcv : 0 < CI.cv.toNat := by decide
    obtain ⟨hPw, -⟩ := trunc_get_some (i := w0.toNat + CI.cv.toNat) (by simpa [aread_apply] using hw) (by omega)
    refine ⟨by simp [hl], fun j hj => ?_⟩
    rcases j with _ | j
    · refine ⟨by simp, ?_⟩
      simp only [nmP, Nat.add_zero, hr0, List.getElem_cons_zero]
      have hrw : rdN P (w0.toNat + CI.cv.toNat) = w := by simp [rdN, hPw]
      rw [hrw]
      exact ⟨hname.symm, hw32, (Array.getElem?_eq_some_iff.mp hPw).1, (Array.getElem?_eq_some_iff.mp hP0).1⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := hall j (by omega)
      refine ⟨by simp; omega, ?_⟩
      simp only [nmP, List.getElem_cons_succ, show bo + (j + 1) = bo + 1 + j by omega] at h2 h3 h4 h5 ⊢
      exact ⟨h2, h3, h4, h5⟩

/-! ## Slices -/

theorem sd_hslice_succ {k : IdxKind} (a : Nat → Option Word) (off n : Nat) :
    (hslice? a off (n + 1) : Option (List (Idx k))) = (do
      let x ← hd? a off
      let xs ← hslice? a (off + 1) n
      pure (x :: xs)) := by
  simp only [hslice?, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  apply congrArg (fun f => List.mapM f (List.range n))
  funext j
  simp only [Function.comp]
  congr 1
  omega

/-- A slice whose words are the handles of `xs` decodes to `xs`. -/
theorem hslice_of {k : IdxKind} {a : Nat → Option Word} : ∀ (xs : List (Idx k)) (o : Nat),
    (∀ j (hj : j < xs.length), ∃ w, a (o + j) = some w ∧ w.toNat < 2 ^ 32 ∧ decI w = xs[j]) →
    hslice? a o xs.length = some xs
  | [], o, _ => rfl
  | x :: xs, o, h => by
    rw [List.length_cons, sd_hslice_succ]
    obtain ⟨w, hw, h32, hx⟩ := h 0 (by simp)
    have h1 : (hd? a o : Option (Idx k)) = some x := by
      simp only [hd?, Nat.add_zero] at hw ⊢; rw [hw]; simp [h32, hx]
    have h2 := hslice_of xs (o + 1) (fun j hj => by
      obtain ⟨w', hw', h', e⟩ := h (j + 1) (by simp; omega)
      exact ⟨w', by rw [show o + 1 + j = o + (j + 1) by omega]; exact hw', h', by simpa using e⟩)
    simp [h1, h2]

end L.Arena
