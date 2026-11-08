module

public import ConAgua.Arena.IndPartsSpec.BlockShapeAllCtorsGo
import ConAgua.Arena.IndPartsSpec.BlockRecNamesUnreserved
import ConRon.Bridge.Grind
public import ConAgua.Arena.IndDecStab

@[expose] public section

/-!
# AllCtors: `ConRon.Arena.BlockShape.allCtors`

The refinement theorems `blockShapeAllCtors_refines` and the lemmas only they use.
-/

noncomputable section

set_option experimental.vcgen true

open ConRon.Arena
open Std.WP
open scoped Lean.Order

namespace L.Ind

open L.Arena

/-! ## Word lists behind a decoded pointer slice -/

theorem decPL_words {m : Mem} {α : Type} {f : Nat → Option α} :
    ∀ (l o : Nat) (xs : List α), decPL m f o l = some xs →
    ∃ ws : List Word, ws.length = l ∧ (∀ j (hj : j < ws.length), (m.arr64 IW)[o + j]? = some ws[j]) ∧
      ws.mapM (fun w => f w.toNat) = some xs
  | 0, o, xs, h => by
    simp only [decPL, List.range_zero, List.mapM_nil, pure, Option.some.injEq] at h
    subst h; exact ⟨[], rfl, fun j hj => absurd hj (by simp), rfl⟩
  | l + 1, o, xs, h => by
    rw [decPL_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨v, hv, x, hx, ys, hys, rfl⟩ := h
    obtain ⟨ws, hlen, hcells, hmap⟩ := decPL_words l (o + 1) ys hys
    simp only [iwN, nat?, iwA, Option.map_eq_some_iff] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    refine ⟨w :: ws, by simp [hlen], fun j hj => ?_, ?_⟩
    · cases j with
      | zero => simpa using hw
      | succ j =>
        have := hcells j (by simpa using hj)
        simpa [Nat.add_assoc, Nat.add_comm 1 j, Nat.add_left_comm] using
          (by rw [show o + (j + 1) = o + 1 + j by omega]; exact this)
    · simp [hx, hmap]

theorem decPL_of_words {m : Mem} {α : Type} {f : Nat → Option α} :
    ∀ (ws : List Word) (o : Nat) (xs : List α),
    (∀ j (hj : j < ws.length), (m.arr64 IW)[o + j]? = some ws[j]) →
    ws.mapM (fun w => f w.toNat) = some xs → decPL m f o ws.length = some xs
  | [], o, xs, _, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h; simp [decPL]
  | w :: ws, o, xs, hc, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    have ih := decPL_of_words ws (o + 1) ys (fun j hj => by
      have := hc (j + 1) (by simpa using hj)
      rw [show o + (j + 1) = o + 1 + j by omega] at this
      simpa using this) hys
    rw [List.length_cons, decPL_succ]
    have hw : iwN m o = some w.toNat := by
      have := hc 0 (by simp)
      simp only [iwN, nat?, iwA, Option.map_eq_some_iff]
      exact ⟨w, by simpa using this, rfl⟩
    rw [hw]
    simp only [bind, Option.bind_some, hx, ih, pure]

/-! ## One member's copy -/

/-- Copying zero words reads no source. -/
theorem copyW_src0 (n : Nat) (m : Mem) (d s : Word) : copyW n m d s 0 = copyW n m d 0 0 := by
  cases n <;> simp [copyW]

theorem ccW_get {n : Nat} {m m1 : Mem} {off q k cl : Word}
    (h : ccW n m off q k = some (cl, m1))
    (hsd : cl.toNat = 0 ∨
      (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2)).toNat + cl.toNat ≤ (q + k).toNat)
    (hd : (q + k).toNat + cl.toNat ≤ (m.arr64 IW).size) (hsz : (m.arr64 IW).size < 2 ^ 64) :
    cl = rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) ∧
    (∀ b : TieredArray, b ≠ ↑IW → m1.arr64 b = m.arr64 b) ∧ (m1.arr64 IW).size = (m.arr64 IW).size ∧
    ∀ i, (m1.arr64 IW)[i]? =
      if (q + k).toNat ≤ i ∧ i < (q + k).toNat + cl.toNat then
        (m.arr64 IW)[(rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2)).toNat + (i - (q + k).toNat)]?
      else (m.arr64 IW)[i]? := by
  cases n with
  | zero => simp [ccW] at h
  | succ n =>
    simp only [ccW] at h
    rcases hc : copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with _ | m2 <;> rw [hc] at h
    · simp at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    rcases hsd with h0 | hsd
    · have hz : rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) = 0 := UInt64.toNat_inj.mp (by simpa using h0)
      rw [hz] at hc hd ⊢
      rw [copyW_src0] at hc
      obtain ⟨hA, hS, hG⟩ := copyW_get n m m2 _ _ _ hc (by simp) hd hsz
      refine ⟨rfl, hA, hS, fun i => ?_⟩
      rw [hG i]
      have : ¬ ((q + k).toNat ≤ i ∧ i < (q + k).toNat + (0 : Word).toNat) := by simp
      rw [ite_eq_right this, ite_eq_right this]
    · exact ⟨rfl, copyW_get n m m2 _ _ _ hc hsd hd hsz⟩

theorem ccW_len {n : Nat} {m m1 : Mem} {off q k cl : Word}
    (h : ccW n m off q k = some (cl, m1)) : cl = rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3) := by
  cases n with
  | zero => simp [ccW] at h
  | succ n =>
    simp only [ccW] at h
    rcases hc : copyW n m (q + k) (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 2))
        (rdW (m.arr64 IW) (rdW (m.arr64 IW) off + 3)) with _ | m2 <;> rw [hc] at h
    · simp at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1.symm

/-- A copy above the original top keeps the pool's growth relation. -/
theorem iwGrow_of_copy {m0 m m1 : Mem} (hg : IWGrow m0 m) (hA : ∀ b : TieredArray, b ≠ ↑IW → m1.arr64 b = m.arr64 b)
    (q : Nat) (hq : iwTop m0 ≤ q)
    (hG : ∀ i, i < q → (m1.arr64 IW)[i]? = (m.arr64 IW)[i]?) : IWGrow m0 m1 := by
  have htop : iwTop m1 = iwTop m := by simp only [iwTop, hA CTL (by decide)]
  have hEr : erTop m1 = erTop m := by simp only [erTop, hA CTL (by decide)]
  refine ⟨?_, ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rw [htop]; exact hg.iw
  · rw [hEr]; exact hg.er
  · rw [hG i (by omega)]; exact hg.iwGet i hi
  · rw [hA EREC (by decide)]; exact hg.erGet i hi

theorem iwN_eq_agree {m m0 : Mem} {q i : Nat} (hag : ∀ j, j < q → (m.arr64 IW)[j]? = (m0.arr64 IW)[j]?)
    (hi : i < q) : iwN m i = iwN m0 i := by
  sorry

/-- A read of the cut pool: below the top, and the pool's own. -/
theorem acTr {m : Mem} {i v : Nat} (h : iwN (truncM m) i = some v) : i < iwTop m ∧ iwN m i = some v := by
  have hi : i < iwTop m := by
    simp only [iwN, nat?, Option.map_eq_some_iff] at h
    obtain ⟨x, hx, -⟩ := h; exact (truncM_iw_get hx).1
  exact ⟨hi, by rw [← iwN_truncM hi]; exact h⟩

/-- A nonempty pointer slice decoded in the cut pool lies below the top. -/
theorem acPLb {α : Type} {m : Mem} {f : Nat → Option α} {o l : Nat} {xs : List α}
    (h : decPL (truncM m) f o l = some xs) : ∀ j < l, o + j < iwTop m := by
  obtain ⟨ws, hl, hc, -⟩ := decPL_words l o xs h
  intro j hj
  exact (truncM_iw_get (hc j (by omega))).1

/-- Constructor records decoded below the tops stay decoded as the pools grow. -/
theorem acMapGrow {m m' : Mem} (hg : IWGrow m m') : ∀ {ws : List Word} {xs : List (IConstantVal × Nat)},
    ws.mapM (fun w => decCN (truncM m) w.toNat) = some xs →
    ws.mapM (fun w => decCN (truncM m') w.toNat) = some xs
  | [], xs, h => h
  | w :: ws, xs, h => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h ⊢
    obtain ⟨x, hx, ys, hys, rfl⟩ := h
    exact ⟨x, DecB.grow (decCN_mono _) hg hx, ys, acMapGrow hg hys, rfl⟩

theorem acGoW_ok (n : Nat) : ∀ (m0 m mf : Mem) (off l q k : Word) (ms : List MemberShape),
    acGoW n m off l q k = some mf → IWGrow m0 m → (m.arr64 IW).size < 2 ^ 64 →
    (∀ i, i < q.toNat → (m.arr64 IW)[i]? = (m0.arr64 IW)[i]?) → iwTop m0 ≤ q.toNat →
    DecB (fun m => decPL m (decMS m) off.toNat l.toNat) m0 ms →
    q.toNat + k.toNat + (ms.map fun x => x.ctors.length).sum ≤ (m.arr64 IW).size →
    ∃ ws : List Word, ws.length = (ms.map fun x => x.ctors.length).sum ∧
      (∀ i (hi : i < ws.length), (mf.arr64 IW)[q.toNat + k.toNat + i]? = some ws[i]) ∧
      ws.mapM (fun w => decCN (truncM m0) w.toNat) = some (ms.map (·.ctors)).flatten ∧
      (∀ i, ¬ (q.toNat + k.toNat ≤ i ∧ i < q.toNat + k.toNat + ws.length) →
        (mf.arr64 IW)[i]? = (m.arr64 IW)[i]?) ∧
      (∀ b : TieredArray, b ≠ ↑IW → mf.arr64 b = m.arr64 b) ∧ (mf.arr64 IW).size = (m.arr64 IW).size := by
  sorry

theorem numCtorsOf_sum (ms : List MemberShape) :
    ConRon.Arena.numCtorsOf ms = (ms.map fun x => x.ctors.length).sum := by
  induction ms with
  | nil => rfl
  | cons a as ih => simp [ConRon.Arena.numCtorsOf, ih]

theorem acW_ok (n : Nat) (m m2 : Mem) (p : Word) (r : List Word) (bs : BlockShape)
    (h : acW n m p = some (r, m2)) (hq : DecB (fun m => decBS m p.toNat) m bs)
    (hsz : (m.arr64 IW).size < 2 ^ 64) (hc : 200 < (m.arr64 CTL).size) :
    ∃ q tot, r = [q, tot] ∧ DecB (fun m => decPL m (decCN m) q.toNat tot.toNat) m2 bs.allCtors ∧
      IWGrow m m2 ∧ MemFrame [IW] [200] m m2 ∧ q.toNat + tot.toNat = iwTop m2 ∧
      q.toNat + tot.toNat ≤ (m.arr64 IW).size := by
  sorry

/-- **`block_shape_all_ctors` refines `BlockShape.allCtors`**: a fresh `IW` slice of the members'
constructor pointers, concatenated, decoded below the tops. The shape decoded below the tops; the
sum's wrap is a capacity (`num_ctors_of` aborts). -/
@[refines ConRon.Arena.BlockShape.allCtors]
theorem blockShapeAllCtors_refines (p : Prog) (ha : p.lookup "iw_alloc" = some iwAlloc)
    (hcp : p.lookup "iw_copy" = some iwCopy) (hnc : p.lookup "num_ctors_of" = some numCtorsOf)
    (hcc : p.lookup "block_shape_ctors_copy" = some blockShapeCtorsCopy)
    (hg : p.lookup "block_shape_all_ctors_go" = some blockShapeAllCtorsGo)
    (hp : p.lookup "block_shape_all_ctors" = some blockShapeAllCtors)
    (n : Nat) (s₀ : St) (a₀ : AState) (dn : NIdx → Option ConLeche.Name) (vis : Word) (fe : IFEnv)
    (q : Word) (bs : BlockShape) (hS : StageR vis fe s₀.mem a₀)
    (hq : DecB (fun m => decBS m q.toNat) s₀.mem bs) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "block_shape_all_ctors" [q]
    ⦃fun r s' => LocEq s' s₀ ∧ StageR vis fe s'.mem a₀ ∧ IWGrow s₀.mem s'.mem ∧
      DecB (fun m => decPL m (decCN m) (r.headD 0).toNat (r.getD 1 0).toNat) s'.mem bs.allCtors ∧
      (r.headD 0).toNat + (r.getD 1 0).toNat ≤ iwTop s'.mem; ⊤⦄ := by
  sorry

end L.Ind

end
