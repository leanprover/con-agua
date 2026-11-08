module

public import ConAgua.Checker.PrepLoopRef
import ConAgua.Checker.PrepCopyRef
import ConAgua.Checker.HoistRef

@[expose] public section

/-!
# `prepare_prelude` refines `preparePrelude` (lane `front4`)

The assembly: two slices (the order `ord`, the marks `mk`), the marks zeroed, the front
(`pFront_ok`: `frontOf`), the rest (`pRest_ok`), the ground hoist (`hNatOpGround_ok`), then `DECL`
rewritten in the hoisted order (`pCopyBack_ok`). The records before are the prelude's then the
stream's (`pre.decls ++ ds`); after, `DECL` represents the prepared array, with the same
per-record facts (`RecOK`), and the store relation and the pins hold at the twin's state after.
-/

open ConRon.Arena ConRon.Arena.Frontend
open L.Arena L.Ind L.Front L.Front.Ind
open Std.WP
open scoped Lean.Order

namespace L.Checker

/-- A record's representation reads its eight words and the pool only. -/
theorem declAtF_congr {D D' P : Array Word} {i j : Nat} {d : IDeclaration}
    (h : ∀ k < 8, dw D' i k = dw D j k) (hd : DeclAtF D P j d) : DeclAtF D' P i d := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  have h6 := h 6 (by decide); have h7 := h 7 (by decide)
  cases d <;> simp_all [DeclAtF, DeclAt, CVAt, IndDeclAt]

theorem recOK_congr {D D' P : Array Word} {i j : Nat} (h : ∀ k < 8, dw D' i k = dw D j k)
    (hd : RecOK D P j) : RecOK D' P i := by
  have h0 := h 0 (by decide); have h1 := h 1 (by decide); have h2 := h 2 (by decide)
  have h3 := h 3 (by decide); have h4 := h 4 (by decide); have h5 := h 5 (by decide)
  simp only [RecOK, h0, h1, h2, h3, h4, h5]
  exact hd

/-- The stream's positions, all unmarked, are the stream. -/
theorem recsAt_range (pre ds : Array IDeclaration) :
    recsAt (pre ++ ds) (List.range' pre.size ds.size) = ds := by
  apply Array.ext
  · simp [recsAt]
  · intro k h1 h2
    simp only [recsAt, List.getElem_toArray, List.getElem_map, List.getElem_range']
    rw [getElem!_pos (pre ++ ds) _ (by simp; omega), Array.getElem_append_right (by omega)]
    congr 1; omega

/-- **`prepare_prelude` on the model**: from the records `pre.decls ++ ds` (the prelude's `np =
CTL[240]` first), when L returns, the twin's `preparePrelude pre ds` succeeds, and `DECL`
represents its result (each record with `RecOK`), the store relation and the pins hold at the
twin's state after, the pool only grew. -/
theorem pPrepCore_ok (p : Prog) (hx : HoistExt p) (n : Nat) (m m' : Mem) (a : AState) (pre : PreludeIx)
    (ds : Array IDeclaration) (np r : Word)
    (hD : ∀ x (h : x < (pre.decls ++ ds).size), DeclAtF (m.arr64 DECL) (m.arr64 DLP) x (pre.decls ++ ds)[x] ∧
      RecOK (m.arr64 DECL) (m.arr64 DLP) x)
    (hn : (rdW (m.arr64 DECL) 0).toNat = (pre.decls ++ ds).size)
    (hnp : np.toNat = pre.decls.size)
    (hDsz : 1 + 8 * (pre.decls ++ ds).size ≤ (m.arr64 DECL).size) (hDsz' : (m.arr64 DECL).size < 2 ^ 64)
    (hA : ArenaR m a) (hseen : ∃ s, SeenR m s) (hnix : ∃ idx, NixR m idx) (hI : IWOK m)
    (hP : PinsR m a.pins) (hnpw : rdW (m.arr64 CTL) 240 = np) (h : pPrepW p n m = some (r, m')) :
    ∃ ds' a', (preparePrelude pre ds).run a = .ok (ds', a') ∧
      (rdW (m'.arr64 DECL) 0).toNat = ds'.size ∧
      (∀ x (h : x < ds'.size), DeclAtF (m'.arr64 DECL) (m'.arr64 DLP) x ds'[x] ∧
        RecOK (m'.arr64 DECL) (m'.arr64 DLP) x) ∧
      ArenaR m' a' ∧ IWOK m' ∧ PinsR m' a'.pins ∧ m'.arr64 DLP = m.arr64 DLP ∧
      (m'.arr64 DECL).size = (m.arr64 DECL).size ∧ a'.store.pers = a.store.pers ∧
      a'.store.scr = a.store.scr ∧ a'.pins = a.pins ∧ ds'.size ≤ (pre.decls ++ ds).size := by
  sorry

/-- **`prepare_prelude()` refines `preparePrelude pre ds`**: from the prelude's records followed by
the stream's in `DECL` (their number in its word `0`, the prelude's in `CTL[240]`), when L returns,
the twin succeeds, `DECL` represents the prepared array (with the same per-record facts), and
the store relation and the pins hold at the twin's state after. (`movedNames`, which
`preparePrelude` drops, is not computed: D30.) -/
@[refines ConRon.Arena.Frontend.preparePrelude]
theorem preparePrelude_refines (p : Prog) (hp : PrepProg p) (hn : PrepExt p) (hh : HoistProg p)
    (hx : HoistExt p) (n : Nat) (s₀ : St) (a : AState) (pre : PreludeIx) (ds : Array IDeclaration)
    (hD : ∀ x (h : x < (pre.decls ++ ds).size),
      DeclAtF (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x (pre.decls ++ ds)[x] ∧
      RecOK (s₀.mem.arr64 DECL) (s₀.mem.arr64 DLP) x)
    (hns : (rdW (s₀.mem.arr64 DECL) 0).toNat = (pre.decls ++ ds).size)
    (hnp : (rdW (s₀.mem.arr64 CTL) 240).toNat = pre.decls.size)
    (hDsz : 1 + 8 * (pre.decls ++ ds).size ≤ (s₀.mem.arr64 DECL).size)
    (hDsz' : (s₀.mem.arr64 DECL).size < 2 ^ 64)
    (hA : ArenaR s₀.mem a) (hseen : ∃ s, SeenR s₀.mem s) (hnix : ∃ idx, NixR s₀.mem idx)
    (hI : IWOK s₀.mem) (hP : PinsR s₀.mem a.pins) :
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "prepare_prelude" []
    ⦃fun _ s' => LocEq s' s₀ ∧ ∃ ds' a', (preparePrelude pre ds).run a = .ok (ds', a') ∧
      (rdW (s'.mem.arr64 DECL) 0).toNat = ds'.size ∧
      (∀ x (h : x < ds'.size), DeclAtF (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x ds'[x] ∧
        RecOK (s'.mem.arr64 DECL) (s'.mem.arr64 DLP) x) ∧
      ArenaR s'.mem a' ∧ IWOK s'.mem ∧ PinsR s'.mem a'.pins ∧ s'.mem.arr64 DLP = s₀.mem.arr64 DLP ∧
      (s'.mem.arr64 DECL).size = (s₀.mem.arr64 DECL).size ∧ a'.store.pers = a.store.pers ∧
      a'.store.scr = a.store.scr ∧ a'.pins = a.pins ∧ ds'.size ≤ (pre.decls ++ ds).size; ⊤⦄ :=
  triple_post (preparePrelude_spec p hp hn hh hx n s₀) (fun r s' h =>
    ⟨h.1, pPrepCore_ok p hx n s₀.mem s'.mem a pre ds _ (r.headD 0) hD hns hnp hDsz hDsz' hA hseen
      hnix hI hP rfl h.2⟩)

attribute [refines ConRon.Arena.Frontend.frontOf] pFront_ok

end L.Checker
