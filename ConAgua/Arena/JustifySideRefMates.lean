module

public import ConAgua.Arena.JustifySideRefSide
public import ConAgua.Arena.JustifySideRefMove
import ConAgua.Census.Attr
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr
import all ConAgua.Arena.JustifySideModels
import all ConAgua.Arena.JustifyIface

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

/-! ## The calls -/

/-- The lookups the record mates take. -/
structure MatesProg (p : Prog) : Prop where
  solution_of : p.lookup "solution_of" = some solutionOfL
  mates_insert : p.lookup "mates_insert" = some matesInsertL
  mates_get : p.lookup "mates_get" = some matesGetL
  mates_set : p.lookup "mates_set" = some matesSetL
  erec_alloc : p.lookup "erec_alloc" = some L.Ind.erecAlloc
  copy_prev : p.lookup "sd_copy_prev" = some sdCopyPrevL
  copy_names : p.lookup "sd_copy_names" = some sdCopyNamesL

theorem copyPrev_call {p : Prog} (hP : MatesProg p) {n : Nat} {m m' : Mem} {d s l : Word} {r : List Word}
    (h : callW p n "sd_copy_prev" [d, s, l] m = some (r, m'))
    (hdl : d.toNat + l.toNat ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64)
    (hsl : s.toNat + l.toNat ≤ d.toNat) :
    CpInv m m' d.toNat (fun j => rdN (m.arr64 EREC) (s.toNat + j)) l.toNat := by
  obtain ⟨s', e', -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (sdCopyPrev_specW p hP.copy_prev n _ d s l) h
  rw [e'] at hw; simp only at hw
  rcases n with _ | n
  · simp [sdCopyPrevW] at hw
  rw [sdCopyPrevW.arm1] at hw
  cases e : sdCopyPrevW.loop1 (n + 1) m d s l 0 with
  | none => rw [e, sdCopyPrevW.k_loop1.eq_1] at hw; cases hw
  | some m₁ =>
    rw [e, sdCopyPrevW.k_loop1.arm1] at hw
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
    exact copyPrev_ok hdl hsz hsl _ _ _ _ (CpInv.start _ _ _) (UInt64.zero_le) e

theorem copyNames_call {p : Prog} (hP : MatesProg p) {n : Nat} {m m' : Mem} {d bo bl : Word}
    {r : List Word} (h : callW p n "sd_copy_names" [d, bo, bl] m = some (r, m'))
    (hdl : d.toNat + bl.toNat ≤ (m.arr64 EREC).size) (hsz : (m.arr64 EREC).size < 2 ^ 64) :
    CpInv m m' d.toNat (fun i => nameW m bo (UInt64.ofNat i)) bl.toNat := by
  obtain ⟨s', e', -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (sdCopyNames_specW p hP.copy_names n _ d bo bl) h
  rw [e'] at hw; simp only at hw
  rcases n with _ | n
  · simp [sdCopyNamesW] at hw
  rw [sdCopyNamesW.eq_2] at hw
  cases e : sdCopyNamesW.loop1 (n + 1) m d bo bl 0 with
  | none => rw [e] at hw; simp [sdCopyNamesW.k_loop1] at hw
  | some m₁ =>
    rw [e, sdCopyNamesW.k_loop1.arm1] at hw
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
    exact copyNames_ok hdl hsz _ _ _ _ (CpInv.start _ _ _) (UInt64.zero_le) e

/-- A tier-0 record-pool word below the top and `2^40`, as `erecP` reads it. -/
theorem erecP_lo {m : Mem} {i : Nat} (h : i < erTop m) (h40 : i < 2 ^ 40) :
    erecP m i = (m.arr64 EREC)[i]? := by
  have a1 : i / 2 ^ 40 % 2 = 0 := by rw [Nat.div_eq_of_lt h40]
  have a2 : i % 2 ^ 40 = i := Nat.mod_eq_of_lt h40
  simp only [erecP, a1, a2, h, ite_true, show i < 2 ^ 64 by omega]

/-! ## One member -/

/-- What the mates' writers keep: only the record pool's tier 0, its top and the mates' rows
change, the pool only grows. -/
structure MKeep (m m' : Mem) : Prop where
  frame : MemFrame [EREC, MATA, MATS, MATN] [129] m m'
  grow : ErecGrow m m'

theorem MKeep.refl (m : Mem) : MKeep m m :=
  ⟨MemFrame.refl _ _ _, ⟨Nat.le_refl _, fun _ _ => rfl, Nat.le_refl _, fun _ _ => rfl⟩⟩

theorem MKeep.trans {m₁ m₂ m₃ : Mem} (h₁ : MKeep m₁ m₂) (h₂ : MKeep m₂ m₃) : MKeep m₁ m₃ :=
  ⟨h₁.frame.trans h₂.frame, ⟨Nat.le_trans h₁.grow.top h₂.grow.top,
    fun i hi => (h₂.grow.get i (Nat.lt_of_lt_of_le hi h₁.grow.top)).trans (h₁.grow.get i hi),
    Nat.le_trans h₁.grow.top1 h₂.grow.top1,
    fun i hi => (h₂.grow.get1 i (Nat.lt_of_lt_of_le hi h₁.grow.top1)).trans (h₁.grow.get1 i hi)⟩⟩

/-- The pool's shape the mates' writers need: the scratch tier off, `EREC` within `2^40` words,
its tier-0 top within it. -/
structure MInv (m : Mem) : Prop where
  off : rdW (m.arr64 CTL) 1 = 0
  size : (m.arr64 EREC).size ≤ 2 ^ 40
  top : erTop m ≤ (m.arr64 EREC).size
  ctl : 228 < (m.arr64 CTL).size

theorem get_of_rdN {a b : Array Word} {i : Nat} (hs : a.size = b.size) (h : rdN a i = rdN b i) :
    a[i]? = b[i]? := by
  by_cases hi : i < b.size
  · simp only [rdN] at h; rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hi] at *
    simpa using h
  · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

theorem matArr_ne (g : Nat) : (matArr g : TieredArray) ≠ EREC ∧ (matArr g : TieredArray) ≠ tier1 EREC ∧
    (matArr g : TieredArray) ≠ CTL ∧ (matArr g : TieredArray) ≠ DLP ∧ (matArr g : TieredArray) ≠ DECL := by
  unfold matArr; split <;> (try split) <;> decide

theorem matSetM_other {m : Mem} {w o l : Word} {b : TieredArray} (hb : b ≠ matArr (rowTag w)) :
    (matSetM m w o l).arr64 b = m.arr64 b := by
  simp only [matSetM]; rw [Mem.arr64_set64_ne _ _ _ _ _ hb, Mem.arr64_set64_ne _ _ _ _ _ hb]

theorem rdN_get {a : Array Word} {i : Nat} (h : i < a.size) : a[i]? = some (rdN a i) := by
  simp [rdN, h]

set_option maxHeartbeats 800000 in
/-- **One block member's mates written** (`mates_insert`'s body at member name `b`): its row
becomes a fresh slice of its old list followed by the block's names `ns`. -/
theorem member_step {p : Prog} (hP : MatesProg p) {n : Nat} {m : Mem} {M : Std.HashMap NIdx (List NIdx)}
    {bo bl : Word} {ns : List NIdx} (hM : MatesR m M) (hI : MInv m) (hbl : bl.toNat < 2 ^ 63)
    (hns : ns.length = bl.toNat)
    (hnm : ∀ i (hi : i < bl.toNat), (decI (nameW m bo (UInt64.ofNat i)) : NIdx) = ns[i]'(by omega))
    {b : Word} (hb32 : b.toNat < 2 ^ 32)
    {ρ1 ρ2 ρ3 ρ4 ρ5 : List Word} {μ1 μ2 μ3 μ4 μ5 : Mem}
    (h1 : callW p n "mates_get" [b] m = some (ρ1, μ1))
    (h2 : callW p n "erec_alloc" [ρ1.tail.headD 0 + bl] μ1 = some (ρ2, μ2))
    (h5 : (ρ1.headD 0 ≠ 0 → callW p n "sd_copy_prev" [ρ2.headD 0, ρ1.headD 0 - 1, ρ1.tail.headD 0] μ2 =
      some (ρ5, μ5)) ∧ (ρ1.headD 0 = 0 → μ5 = μ2))
    (h3 : callW p n "sd_copy_names" [ρ2.headD 0 + ρ1.tail.headD 0, bo, bl] μ5 = some (ρ3, μ3))
    (h4 : callW p n "mates_set" [b, ρ2.headD 0 + 1, ρ1.tail.headD 0 + bl] μ3 = some (ρ4, μ4)) :
    MatesR μ4 (M.insert (decI b) (M.getD (decI b) [] ++ ns)) ∧ MInv μ4 ∧ MKeep m μ4 := by
  -- mates_get
  obtain ⟨t1, e1, hm1, -, hr1⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (matesGet_spec p hP.mates_get n _ b) h1
  simp only at hm1 hr1
  have em1 : μ1 = m := e1 ▸ hm1
  clear e1 hm1; subst μ1; subst hr1
  simp only [List.headD_cons, List.tail_cons] at h2 h5 h3 h4
  generalize ho : (matRow m b).1 = o at h2 h5 h3 h4
  generalize hl : (matRow m b).2 = l at h2 h5 h3 h4
  -- erec_alloc
  obtain ⟨t2, e2, -, hw2⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (L.Ind.erecAlloc_specW p hP.erec_alloc n _ (l + bl)) h2
  rw [e2] at hw2; simp only [L.Ind.erAllocW, hI.off, ite_true] at hw2
  split at hw2; · cases hw2
  split at hw2; · cases hw2
  rename_i c1 c2
  obtain ⟨hd2, hμ2⟩ := Prod.mk.inj (Option.some.inj hw2)
  subst μ2
  generalize hd : rdW (m.arr64 CTL) 129 = d at hd2 c1 c2
  have hdtop : d.toNat = erTop m := by rw [← hd]; rfl
  simp only [← hd2, List.headD_cons] at h5 h3 h4
  have hsz := hI.size
  have hlen : (Mem.len64 m EREC).toNat = (m.arr64 EREC).size := by
    simp [Mem.len64]; omega
  have c1' : d.toNat ≤ (m.arr64 EREC).size := by
    have := UInt64.not_lt.mp c1; have := UInt64.le_iff_toNat_le.mp this; omega
  -- the old list's length
  have hlb : l.toNat ≤ erTop m := by
    by_cases o0 : o = 0
    · have := hM.z b (by rw [ho]; exact o0); rw [hl] at this; subst this; simp
    · have := (hM.ok b (by rw [ho]; exact o0)).1; rw [ho, hl] at this; omega
  have hlbl : (l + bl).toNat = l.toNat + bl.toNat := by
    rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by have := hI.top; omega)
  have c2' : l.toNat + bl.toNat ≤ (m.arr64 EREC).size - d.toNat := by
    have := UInt64.not_lt.mp c2
    have := UInt64.le_iff_toNat_le.mp this
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.not_lt.mp c1), hlen, hlbl] at this; omega
  have hm2 : L.Ind.erAllocMem m (l + bl) = m.set64 CTL 129 (d + (l + bl)) := by
    simp [L.Ind.erAllocMem, hI.off, hd]
  rw [← hμ2, hm2] at h5
  generalize hM2 : m.set64 CTL 129 (d + (l + bl)) = m2 at h5
  have m2a : ∀ x : TieredArray, x ≠ CTL → m2.arr64 x = m.arr64 x := fun x hx => by
    rw [← hM2, Mem.arr64_set64_ne _ _ _ _ _ hx]
  have m2c : ∀ x : Word, x ≠ 129 → rdW (m2.arr64 CTL) x = rdW (m.arr64 CTL) x := fun x hx => by
    rw [← hM2, rdW_set64]; simp [Ne.symm hx]
  have m2s : ∀ x, (m2.arr64 x).size = (m.arr64 x).size := fun x => by rw [← hM2, size_set64_any]
  have hdl : (d + l).toNat = d.toNat + l.toNat := by rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have hdk : (d + (l + bl)).toNat = d.toNat + l.toNat + bl.toNat := by
    rw [UInt64.toNat_add, hlbl, Nat.mod_eq_of_lt (by omega)]; omega
  have m2t : erTop m2 = d.toNat + l.toNat + bl.toNat := by
    simp only [erTop, ← hM2, rdW_set64]
    simp only [show (129 : Word).toNat < (m.arr64 CTL).size by have := hI.ctl; simp; omega, and_self,
      ite_true, hdk]
  -- the old list
  have hE2 : m2.arr64 EREC = m.arr64 EREC := m2a _ (by decide)
  have hC5 : CpInv m2 μ5 d.toNat (fun j => rdN (m.arr64 EREC) (o.toNat - 1 + j)) l.toNat := by
    by_cases o0 : o = 0
    · rw [h5.2 o0]
      have := hM.z b (by rw [ho]; exact o0); rw [hl] at this; subst this
      exact CpInv.start _ _ _
    · have ho1 : (1 : Word) ≤ o := UInt64.le_iff_toNat_le.mpr (by
        have : o.toNat ≠ 0 := fun h => o0 (UInt64.toNat_inj.mp (by simpa using h))
        simp; omega)
      have hc := copyPrev_call hP (h5.1 o0) (by rw [m2s]; omega) (by rw [m2s]; omega)
        (by have := (hM.ok b (by rw [ho]; exact o0)).1; rw [ho, hl] at this
            rw [UInt64.toNat_sub_of_le _ _ ho1]; simp; omega)
      rw [hE2] at hc
      rwa [UInt64.toNat_sub_of_le _ _ ho1, show (1 : Word).toNat = 1 from rfl] at hc
  -- the names
  have hC3 := copyNames_call hP h3 (by rw [hdl, hC5.size, m2s]; omega) (by rw [hC5.size, m2s]; omega)
  rw [hdl] at hC3
  have hP5 : μ5.arr64 DLP = m.arr64 DLP := by rw [hC5.other _ (by decide), m2a _ (by decide)]
  have hnw : ∀ i, nameW μ5 bo i = nameW m bo i := fun i => by simp only [nameW, hP5]
  -- mates_set
  obtain ⟨t4, e4, -, ht0, htg, hm4, hbd⟩ := triple_of_callW (s₀ := ⟨μ3, Locals.init []⟩)
    (matesSet_spec p hP.mates_set n _ b (d + 1) (l + bl)) h4
  simp only at hm4 hbd
  have em4 : μ4 = matSetM μ3 b (d + 1) (l + bl) := e4 ▸ hm4
  clear e4 hm4; subst em4
  have hA3 : ∀ x : TieredArray, x ≠ EREC → x ≠ CTL → μ3.arr64 x = m.arr64 x := fun x h1 h2 => by
    rw [hC3.other x h1, hC5.other x h1, m2a x h2]
  have hC3c : μ3.arr64 CTL = m2.arr64 CTL := by rw [hC3.other _ (by decide), hC5.other _ (by decide)]
  have hE3s : (μ3.arr64 EREC).size = (m.arr64 EREC).size := by rw [hC3.size, hC5.size, m2s]
  have hrows : ∀ w, matRow μ3 w = matRow m w := fun w => by
    simp only [matRow, hA3 _ (matArr_ne _).1 (matArr_ne _).2.2.1]
  have t3 : erTop μ3 = d.toNat + l.toNat + bl.toNat := by simp only [erTop, hC3c]; exact m2t
  have hgrow : ErecGrow m μ3 := ⟨by rw [t3, ← hdtop]; omega, fun i hi => by
      rw [← hdtop] at hi
      apply get_of_rdN (by rw [hE3s])
      rw [hC3.out i (.inl (by omega)), hC5.out i (.inl hi), hE2],
    by simp only [erecTop1, hC3c, m2c 130 (by decide)]; exact Nat.le_refl _,
    fun i _ => by rw [hA3 _ (by decide) (by decide)]⟩
  have hM3 := hM.grow hrows hgrow
  have hgd : M.getD (decI b) [] = (matList m b).getD [] := by
    have := hM.get (decI b); rw [decI_word_self _ hb32] at this
    simp only [Std.HashMap.getD_eq_getD_getElem?, this]
  -- the new slice
  have hnew : ∀ (prev : List NIdx) (_hpl0 : prev.length = l.toNat),
      (∀ j (hj : j < l.toNat), ∃ w, erecP m (o.toNat - 1 + j) = some w ∧ w.toNat < 2 ^ 32 ∧
        decI w = prev[j]'(by omega)) →
      hslice? (erecP μ3) d.toNat (l + bl).toNat = some (prev ++ ns) := by
    intro prev hpl hpw
    rw [hlbl, ← hpl, ← hns, ← List.length_append]
    apply hslice_of
    intro j hj
    simp only [List.length_append, hpl, hns] at hj
    have hin : d.toNat + j < (μ3.arr64 EREC).size := by
      rw [hE3s]; have := c2'; have := c1'; have := hpl; have := hns; omega
    refine ⟨rdN (μ3.arr64 EREC) (d.toNat + j), ?_, ?_⟩
    · rw [erecP_lo (by rw [t3]; omega) (by omega)]; exact rdN_get hin
    by_cases jl : j < l.toNat
    · obtain ⟨w, hw, hw32, hdw⟩ := hpw j jl
      have hok : o.toNat - 1 + l.toNat ≤ erTop m := by
        by_cases o0 : o = 0
        · have := hM.z b (by rw [ho]; exact o0); rw [hl] at this; subst this; simp at jl
        · have := (hM.ok b (by rw [ho]; exact o0)).1; rw [ho, hl] at this; omega
      have hlo : erecP m (o.toNat - 1 + j) = (m.arr64 EREC)[o.toNat - 1 + j]? :=
        erecP_lo (by omega) (by have := hI.top; omega)
      rw [hlo] at hw
      have hv : rdN (μ3.arr64 EREC) (d.toNat + j) = w := by
        rw [hC3.out _ (.inl (by omega)), hC5.done j jl]
        simp only [rdN, hw, Option.getD_some]
      rw [hv]; refine ⟨hw32, ?_⟩
      rw [List.getElem_append_left (by omega)]; exact hdw
    · have hv : rdN (μ3.arr64 EREC) (d.toNat + j) = nameW m bo (UInt64.ofNat (j - l.toNat)) := by
        have := hC3.done (j - l.toNat) (by omega)
        rw [show d.toNat + l.toNat + (j - l.toNat) = d.toNat + j by omega] at this
        rw [this, hnw]
      rw [hv]; refine ⟨mask_lt _, ?_⟩
      rw [List.getElem_append_right (by omega)]
      simp only [hpl]
      exact hnm _ (by omega)
  have hprev : hslice? (erecP μ3) d.toNat (l + bl).toNat = some (M.getD (decI b) [] ++ ns) := by
    rw [hgd]
    by_cases o0 : o = 0
    · have hl0 := hM.z b (by rw [ho]; exact o0); rw [hl] at hl0; subst hl0
      have : matList m b = none := by simp [matList, ho, o0]
      rw [this]
      exact hnew [] rfl (fun j hj => absurd hj (by simp))
    · obtain ⟨prev, hpv⟩ := Option.isSome_iff_exists.mp (hM.ok b (by rw [ho]; exact o0)).2
      rw [hpv]
      have hpv' := hpv; simp only [matList, ho, hl, o0, ite_false] at hpv'
      obtain ⟨hplen, hget⟩ := hslice?_get hpv'
      refine hnew prev hplen (fun j hj => ?_)
      obtain ⟨w, hw, h32, hx⟩ := hget j hj
      refine ⟨w, hw, h32, ?_⟩
      rw [List.getElem?_eq_getElem (by omega)] at hx; exact (Option.some.inj hx).symm
  have hMR := hM3.set hb32 htg ht0 hbd (by omega) hprev (by rw [t3, hlbl]; omega)
  -- the shape and the frame
  have hm4o : ∀ x : TieredArray, x ≠ matArr (rowTag b) → (matSetM μ3 b (d + 1) (l + bl)).arr64 x = μ3.arr64 x :=
    fun x hx => matSetM_other hx
  have h4c := hm4o _ (matArr_ne _).2.2.1.symm
  have h4e := hm4o _ (matArr_ne _).1.symm
  refine ⟨hMR, ⟨?_, ?_, ?_, ?_⟩, ⟨⟨fun x hx hx' => ?_, fun x hx => ?_, fun x => ?_⟩, ?_⟩⟩
  · rw [h4c, hC3c, m2c 1 (by decide)]; exact hI.off
  · rw [h4e, hE3s]; exact hI.size
  · rw [show erTop (matSetM μ3 b (d + 1) (l + bl)) = erTop μ3 by simp only [erTop, h4c], t3, h4e, hE3s]
    omega
  · simp only [matSetM, size_set64_any]; rw [hC3c, m2s]; exact hI.ctl
  · have hne : x ≠ matArr (rowTag b) := fun e => by
      apply hx; rw [e]; unfold matArr; split <;> (try split) <;> simp
    rw [hm4o x hne, hA3 x (fun e => hx (by simp [e])) hx']
  · rw [h4c, hC3c]; exact m2c x (fun e => hx (by simp [e]))
  · simp only [matSetM, size_set64_any]
    by_cases e : x = EREC
    · subst e; exact hE3s
    · by_cases e' : x = CTL
      · subst e'; rw [hC3c, m2s]
      · rw [hA3 x e e']
  · exact ⟨by simp only [erTop, h4c]; exact hgrow.top, fun i hi => by rw [h4e]; exact hgrow.get i hi,
      by simp only [erecTop1, h4c]; exact hgrow.top1,
      fun i hi => by rw [hm4o _ (matArr_ne _).2.1.symm]; exact hgrow.get1 i hi⟩

/-! ## `mates_insert` -/

theorem nidxAppend_all (acc ns : List NIdx) : nidxAppend acc ns 0 ns.length = acc ++ ns := by
  simp [nidxAppend]

theorem matesInsert_cons (M : Std.HashMap NIdx (List NIdx)) (ns : List NIdx) (c : IConstantInfo)
    (cs : List IConstantInfo) :
    matesInsert M ns (c :: cs) = matesInsert (M.insert c.name (M.getD c.name [] ++ ns)) ns cs := by
  simp [matesInsert, nidxAppend_all]

/-- **`mates_insert(bo, bl, j)` refines `matesInsert`** over the block's members from `j`: the
block `block` (its names in `DLP`, `nameW`), `ns` its names. -/
theorem matesInsert_ok {p : Prog} (hP : MatesProg p) {m₀ : Mem} {bo bl : Word}
    {block : List IConstantInfo} (hbl : bl.toNat < 2 ^ 63) (hlen : block.length = bl.toNat)
    (hnm : ∀ i (hi : i < bl.toNat), (decI (nameW m₀ bo (UInt64.ofNat i)) : NIdx) =
      (block[i]'(by omega)).name) :
    ∀ n (m m' : Mem) (x j : Word) (M : Std.HashMap NIdx (List NIdx)),
      MatesR m M → MInv m → MKeep m₀ m → j ≤ bl →
      matesInsertW p n m bo bl j = some (x, m') →
      MatesR m' (matesInsert M (block.map (·.name)) (block.drop j.toNat)) ∧ MInv m' ∧ MKeep m₀ m' := by
  intro n
  induction n with
  | zero => intro m m' x j M _ _ _ _ h; rw [matesInsertW.eq_1] at h; cases h
  | succ n ih =>
    intro m m' x j M hM hI hK hj h
    have hns : (block.map (·.name)).length = bl.toNat := by simp [hlen]
    have hP0 : m.arr64 DLP = m₀.arr64 DLP := hK.frame.arr _ (by decide) (by decide)
    have hnw : ∀ i, nameW m bo i = nameW m₀ bo i := fun i => by simp only [nameW, hP0]
    by_cases g : bl ≤ j
    · rw [matesInsertW.arm1 _ _ _ _ _ _ g] at h
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
      have : j = bl := UInt64.le_antisymm hj g
      subst this
      rw [List.drop_of_length_le (by omega)]
      exact ⟨by simpa [matesInsert] using hM, hI, hK⟩
    rw [matesInsertW.arm2 _ _ _ _ _ _ g] at h
    have gj : j.toNat < bl.toNat := UInt64.lt_iff_toNat_lt.mp (UInt64.not_le.mp g)
    generalize hb : rdW (m.arr64 DLP) (rdW (m.arr64 DLP) (bo + j) + (CI.cv + CV.name)) &&& 4294967295 = b at h
    have hbn : b = nameW m bo j := hb.symm
    cases h1 : callW p n "mates_get" [b] m with
    | none => rw [h1] at h; simp at h
    | some q1 =>
    obtain ⟨ρ1, μ1⟩ := q1
    rw [h1, L.Ind.bW_some] at h
    cases h2 : callW p n "erec_alloc" [ρ1.tail.headD 0 + bl] μ1 with
    | none => rw [h2] at h; simp at h
    | some q2 =>
    obtain ⟨ρ2, μ2⟩ := q2
    rw [h2, L.Ind.bW_some] at h
    -- the old list's copy, or none
    obtain ⟨ρ5, μ5, h5, hj1⟩ : ∃ ρ5 μ5, ((ρ1.headD 0 ≠ 0 →
        callW p n "sd_copy_prev" [ρ2.headD 0, ρ1.headD 0 - 1, ρ1.tail.headD 0] μ2 = some (ρ5, μ5)) ∧
        (ρ1.headD 0 = 0 → μ5 = μ2)) ∧
        matesInsertW.j1 p n bo bl j b (ρ1.tail.headD 0) (ρ2.headD 0) μ5 = some (x, m') := by
      by_cases c : ρ1.headD 0 ≠ 0
      · rw [ite_eq_left c] at h
        cases h5 : callW p n "sd_copy_prev" [ρ2.headD 0, ρ1.headD 0 - 1, ρ1.tail.headD 0] μ2 with
        | none => rw [h5] at h; simp at h
        | some q5 =>
          obtain ⟨ρ5, μ5⟩ := q5
          rw [h5, L.Ind.bW_some] at h
          exact ⟨ρ5, μ5, ⟨fun _ => rfl, fun e => absurd e c⟩, h⟩
      · rw [ite_eq_right c] at h
        exact ⟨[], μ2, ⟨fun e => absurd e c, fun _ => rfl⟩, h⟩
    rw [matesInsertW.j1.arm1] at hj1
    cases h3 : callW p n "sd_copy_names" [ρ2.headD 0 + ρ1.tail.headD 0, bo, bl] μ5 with
    | none => rw [h3] at hj1; simp at hj1
    | some q3 =>
    obtain ⟨ρ3, μ3⟩ := q3
    rw [h3, L.Ind.bW_some] at hj1
    cases h4 : callW p n "mates_set" [b, ρ2.headD 0 + 1, ρ1.tail.headD 0 + bl] μ3 with
    | none => rw [h4] at hj1; simp at hj1
    | some q4 =>
    obtain ⟨ρ4, μ4⟩ := q4
    rw [h4, L.Ind.bW_some] at hj1
    cases hr : matesInsertW p n μ4 bo bl (j + 1) with
    | none => rw [hr, matesInsertW.k_mates_insert.none] at hj1; cases hj1
    | some q =>
    obtain ⟨y, m₁⟩ := q
    rw [hr, matesInsertW.k_mates_insert.arm1] at hj1
    obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hj1)
    have hb32 : b.toNat < 2 ^ 32 := by rw [← hb]; exact mask_lt _
    obtain ⟨hM4, hI4, hK4⟩ := member_step hP hM hI hbl hns
      (fun i hi => by rw [hnw, hnm i hi]; simp) hb32 h1 h2 h5 h3 h4
    have e1 : (j + 1).toNat = j.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have := ih μ4 m₁ y (j + 1) _ hM4 hI4 (hK.trans hK4)
      (UInt64.le_iff_toNat_le.mpr (by rw [e1]; omega)) hr
    rw [e1] at this
    rw [List.drop_eq_getElem_cons (by omega), matesInsert_cons]
    have hname : (decI b : NIdx) = (block[j.toNat]'(by omega)).name := by
      rw [hbn, hnw, ← hnm j.toNat gj]; simp
    rw [← hname]
    exact this

/-! ## `solution_of` -/

theorem cvname_eq : (CI.cv + CV.name : Word) = CI.cv := by decide

/-- The block of an inductive record, its names as `mates_insert` reads them. -/
theorem block_of_rec {D P : Array Word} {ds : Array IDeclaration} (hD : DeclsF D P ds) {k : Nat}
    (hk : k < ds.size) (hR : L.Checker.RecOK D P k) {block : List IConstantInfo} {nP : Nat}
    (he : ds[k] = .indDecl block nP) {m : Mem} (hP : m.arr64 DLP = P) :
    block.length = (dw D k 3).toNat ∧ (dw D k 3).toNat < 2 ^ 63 ∧
      ∀ i (hi : i < block.length), (decI (nameW m (dw D k 2) (UInt64.ofNat i)) : NIdx) = block[i].name := by
  have hr := hD.recs k hk
  rw [he] at hr
  obtain ⟨h6, -, t, -, hdec⟩ := hr
  obtain ⟨hbo, hp, -⟩ := hR.2 h6
  obtain ⟨hlen, hall⟩ := block_names_dec _ _ block hdec (by omega) (fun j hj => by
    have := hp j hj; simpa [rdN] using this)
  have hps := hD.psize
  refine ⟨hlen, ?_, fun i hi => ?_⟩
  · rcases Nat.eq_zero_or_pos (dw D k 3).toNat with h0 | h0
    · rw [h0]; decide
    · obtain ⟨-, -, -, -, h5⟩ := hall ((dw D k 3).toNat - 1) (by omega); omega
  obtain ⟨hi', hname, -, hq, hbi⟩ := hall i (by omega)
  have e1 : (dw D k 2 + UInt64.ofNat i).toNat = (dw D k 2).toNat + i := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by have := hbi; have := hps; simp only [UInt64.size] at *; omega)]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : (rdN P ((dw D k 2).toNat + i) + (CI.cv + CV.name)).toNat =
      (rdN P ((dw D k 2).toNat + i)).toNat + CI.cv.toNat := by
    rw [cvname_eq, UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by omega)
  have : nameW m (dw D k 2) (UInt64.ofNat i) = nmP P (dw D k 2).toNat i &&& 4294967295 := by
    simp only [nameW, hP, rdW_rdN, e1, e2, nmP]
  rw [this, decI_mask]; exact hname

theorem sd_kind6 {D P : Array Word} {x : Nat} {d : IDeclaration} (h : DeclAtF D P x d)
    (h6 : dw D x 0 = 6) : ∃ b nP, d = .indDecl b nP := by
  cases d with
  | indDecl b nP => exact ⟨b, nP, rfl⟩
  | _ => simp only [DeclAtF, DeclAt] at h; rw [h.1] at h6; cases h6

theorem recordMatesGo_other (M : Std.HashMap NIdx (List NIdx)) (d : IDeclaration)
    (ds : List IDeclaration) (h : ∀ b nP, d ≠ .indDecl b nP) :
    recordMatesGo M (d :: ds) = recordMatesGo M ds := by
  cases d <;> first | rfl | exact absurd rfl (h _ _)

theorem solutionOfLoop_ok {p : Prog} (hP : MatesProg p) {cnt : Word} {ds : Array IDeclaration}
    {m₀ : Mem} (hcnt : cnt.toNat = ds.size) (hD : DeclsF (m₀.arr64 DECL) (m₀.arr64 DLP) ds)
    (hR : ∀ x < ds.size, L.Checker.RecOK (m₀.arr64 DECL) (m₀.arr64 DLP) x) :
    ∀ n (m m' : Mem) (k : Word) (M : Std.HashMap NIdx (List NIdx)),
      MatesR m M → MInv m → MKeep m₀ m → k.toNat ≤ ds.size →
      solutionOfW.loop1 p n m cnt k = some m' →
      MatesR m' (recordMatesGo M (ds.toList.drop k.toNat)) ∧ MInv m' ∧ MKeep m₀ m' := by
  intro n
  induction n with
  | zero => intro m m' k M _ _ _ _ h; rw [solutionOfW.loop1.eq_1] at h; cases h
  | succ n ih =>
    intro m m' k M hM hI hK hk h
    by_cases g : k < cnt
    · have gk : k.toNat < ds.size := by rw [← hcnt]; exact UInt64.lt_iff_toNat_lt.mp g
      have hk60 : k.toNat < 2 ^ 60 := by have := hD.room; have := hD.dsize; omega
      have hDm : m.arr64 DECL = m₀.arr64 DECL := hK.frame.arr _ (by decide) (by decide)
      have hPm : m.arr64 DLP = m₀.arr64 DLP := hK.frame.arr _ (by decide) (by decide)
      have e0 := sd_rdW_dw (m.arr64 DECL) k 1 0 rfl (by decide) hk60
      have e2 := sd_rdW_dw (m.arr64 DECL) k 3 2 rfl (by decide) hk60
      have e3 := sd_rdW_dw (m.arr64 DECL) k 4 3 rfl (by decide) hk60
      have ek : (k + 1).toNat = k.toNat + 1 := by
        rw [UInt64.toNat_add]; have := UInt64.toNat_lt cnt; simp; omega
      rw [List.drop_eq_getElem_cons (by simpa using gk)]
      simp only [Array.getElem_toList]
      by_cases k6 : dw (m₀.arr64 DECL) k.toNat 0 = 6
      · obtain ⟨block, nP, he⟩ := sd_kind6 (hD.recs k.toNat gk) k6
        rw [solutionOfW.loop1.arm1 _ _ _ _ _ g (by rw [e0, hDm, k6])] at h
        rw [e2, e3, hDm] at h
        cases h1 : callW p n "mates_insert" [dw (m₀.arr64 DECL) k.toNat 2, dw (m₀.arr64 DECL) k.toNat 3, 0] m with
        | none => rw [h1] at h; simp at h
        | some q =>
        obtain ⟨ρ, μ⟩ := q
        rw [h1, L.Ind.bW_some, solutionOfW.j1.arm1] at h
        obtain ⟨t, et, -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
          (matesInsert_specW p hP.mates_insert n _ _ _ 0) h1
        rw [et] at hw; simp only at hw
        obtain ⟨hlen, hbl, hnm⟩ := block_of_rec hD gk (hR _ gk) he hPm
        obtain ⟨hM1, hI1, hK1⟩ := matesInsert_ok hP (m₀ := m) hbl hlen (fun i hi => hnm i (by omega))
          n m μ _ 0 M hM hI (MKeep.refl m) (UInt64.zero_le) hw
        have := ih μ m' (k + 1) _ hM1 hI1 (hK.trans hK1) (by rw [ek]; omega) h
        rw [he, ek] at *
        simpa [recordMatesGo] using this
      · rw [solutionOfW.loop1.arm2 _ _ _ _ _ g (by rw [e0, hDm]; exact k6), solutionOfW.j1.arm1] at h
        have := ih m m' (k + 1) M hM hI hK (by rw [ek]; omega) h
        rw [ek] at this
        rw [recordMatesGo_other _ _ _ (fun b nP e => by
          have hr := hD.recs k.toNat gk; rw [e] at hr; exact k6 hr.1)]
        exact this
    · rw [solutionOfW.loop1.arm3 _ _ _ _ _ g] at h; cases h
      have : k.toNat = ds.size := by
        have := UInt64.le_iff_toNat_le.mp (UInt64.not_lt.mp g); omega
      rw [this, List.drop_of_length_le (by simp)]
      exact ⟨by simpa [recordMatesGo] using hM, hI, hK⟩

/-- **`solution_of(cnt)` refines `solutionOf`'s record mates** (`recordMatesGo ∅` over the
front's `cnt` records): from empty rows, a returning run leaves the twin's map in the rows
(`MatesR`), only the record pool's tier 0, its top and the rows changed. -/
@[refines ConRon.Arena.recordMatesGo ConRon.Arena.matesInsert]
theorem solutionOf_ref {p : Prog} (hP : MatesProg p) {n : Nat} {cnt : Word} {m m' : Mem}
    {r : List Word} {ds : Array IDeclaration}
    (hc : callW p n "solution_of" [cnt] m = some (r, m'))
    (hD : DeclsF (m.arr64 DECL) (m.arr64 DLP) ds)
    (hR : ∀ x < ds.size, L.Checker.RecOK (m.arr64 DECL) (m.arr64 DLP) x) (hcnt : cnt.toNat = ds.size)
    (hz : ∀ g ≤ 2, ∀ j, rdN (m.arr64 (matArr g)) j = 0)
    (hsz : (m.arr64 EREC).size ≤ 2 ^ 40) (htop : erTop m ≤ (m.arr64 EREC).size)
    (hctl : 228 < (m.arr64 CTL).size) :
    MatesR m' (recordMatesGo ∅ ds.toList) ∧ MInv m' ∧ MKeep m m' := by
  obtain ⟨t, et, -, hw⟩ := triple_of_callW (s₀ := ⟨m, Locals.init []⟩)
    (solutionOf_specW p hP.solution_of n _ cnt) hc
  rw [et] at hw; simp only at hw
  rcases n with _ | n
  · rw [solutionOfW.eq_1] at hw; cases hw
  by_cases c : rdW (m.arr64 CTL) 1 = 0
  · rw [solutionOfW.arm1 _ _ _ _ c] at hw
    cases e : solutionOfW.loop1 p (n + 1) m cnt 0 with
    | none => rw [e] at hw; simp [solutionOfW.k_loop1] at hw
    | some m₁ =>
      rw [e, solutionOfW.k_loop1.arm1] at hw
      obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj hw)
      have := solutionOfLoop_ok hP hcnt hD hR (n + 1) m m₁ 0 ∅ (MatesR.zero hz) ⟨c, hsz, htop, hctl⟩
        (MKeep.refl m) (Nat.zero_le _) e
      simpa using this
  · rw [solutionOfW.abort1 _ _ _ _ c] at hw; cases hw

/-! ## The solution -/

/-- **The solution's index part across the mates' writers.** -/
theorem SolIdxR.keep {m m' : Mem} {I : IStreamIndex} (h : SolIdxR m I) (hk : MKeep m m') :
    SolIdxR m' I := by
  have hx := hk.grow.ext
  have hs : ∀ g, m'.arr64 (sixArr g) = m.arr64 (sixArr g) := fun g => hk.frame.arr _
    (by unfold sixArr; split <;> (try split) <;> decide) (by unfold sixArr; split <;> (try split) <;> decide)
  have ht : ∀ g, m'.arr64 (stxArr g) = m.arr64 (stxArr g) := fun g => hk.frame.arr _
    (by unfold stxArr; split <;> (try split) <;> decide) (by unfold stxArr; split <;> (try split) <;> decide)
  have hr : ∀ w, solRow m' w = solRow m w := fun w => by simp only [solRow, hs]
  have hb : ∀ w, solTbl m' w = solTbl m w := fun w => by simp only [solTbl, ht]
  refine ⟨fun n => ?_, fun n => ?_, ?_, ?_, fun w => by rw [hr, hb]; exact h.rows w⟩
  · have := h.base n; rw [hr, this]; split
    · rfl
    · cases e : I.base.idx[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decCI this.2.symm]
  · have := h.btbl n; rw [hb, this]; split
    · rfl
    · cases e : I.base.tbls[n]? with
      | none => rw [e] at this; simp_all
      | some y =>
        rw [e] at this
        simp only [Option.map_some, ite_eq_right_of_eq_false _ _ (eq_false ‹_›), Option.some.injEq,
          Prod.mk.injEq] at this
        rw [← this.2, hx.decTbl this.2.symm]
  · rw [ctlW, hk.frame.ctl _ (by decide)]; exact h.next
  · rw [ctlW, hk.frame.ctl _ (by decide)]; exact h.size

/-- **The solution in L** (`solutionOf`): the moved index (`index_to_solution`, `SolIdxR`) and the
record mates (`solution_of`, `MatesR`). -/
@[refines ConRon.Arena.solutionOf]
theorem solR_of {m m' : Mem} {I : IStreamIndex} {ds : List IDeclaration} (hI : SolIdxR m I)
    (hM : MatesR m' (recordMatesGo ∅ ds)) (hk : MKeep m m') : SolR m' (solutionOf I ds) :=
  SolR.ofIdx (hI.keep hk) hM.get (fun w hw => (hM.ok w hw).2)

end L.Arena
