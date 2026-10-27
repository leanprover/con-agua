import ConAgua.Arena.DeclAndPin
import ConAgua.Arena.GrindAttr
import ConAgua.L.GrindAttr

/-!
# The `And` pin's inductive arm, part 1: `and_block_named(bo, bl)` refines `blockAndNamed`

The front's inductive record `i` (`IndDeclAt`, `StateDR.lean`) is a slice `DLP[bo ‥ bo + bl)` of
pointers to constant records in `DLP` (`decCI`'s layout, the name at word `+ 1`), decoded in the
pool cut at some `t` (`trunc`: word `0` cleared). `and_block_named(bo, bl)` reads the same words in
`DLP` itself; the two agree on every word but `0`, so the slice must not start at word `0` (a
pointer read there is `0` in the cut pool and the top in `DLP`). With the three pinned `And` names
`PINS[12]`, `PINS[49]`, `PINS[50]` below `2^32` (a filled pin table, `PinsFull`), its result is
`blockAndNamed hs block` (`abnW_eq`), `hs` the handles `andPinNameHs` reads (`andPinNameHs_run`).
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option experimental.vcgen true

namespace L.Arena

open L.Front (DECL DLP IndDeclAt dw trunc decCIs)

/-! ## The word model -/

/-- The name test on the record the pointer `DLP[bo]` names. -/
def abnHit (m : Mem) (bo : Word) : Prop :=
  lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) = rdW (m.arr64 PINS) 12 ∨
  lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) = rdW (m.arr64 PINS) 49 ∨
  lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) = rdW (m.arr64 PINS) 50

instance (m : Mem) (bo : Word) : Decidable (abnHit m bo) := by unfold abnHit; infer_instance

/-- **The model of `and_block_named(bo, bl)`**, by the slice's length. -/
def abnW (m : Mem) : Word → Nat → Word
  | _, 0 => 0
  | bo, k + 1 => if abnHit m bo then 1 else abnW m (bo + 1) k

theorem abnW_zero (m : Mem) (bo bl : Word) (h : bl = 0) : abnW m bo bl.toNat = 0 := by
  subst h; rfl

theorem abnW_hit (m : Mem) (bo bl : Word) (h : bl ≠ 0)
    (hh : lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) = rdW (m.arr64 PINS) 12 ∨
      lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) = rdW (m.arr64 PINS) 49 ∨
      lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) = rdW (m.arr64 PINS) 50) :
    abnW m bo bl.toNat = 1 := by
  have hb : bl.toNat = (bl - 1).toNat + 1 := by
    have : bl.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
    have := bl.toNat_lt
    rw [UInt64.toNat_sub]; simp; omega
  rw [hb]; simp only [abnW, abnHit]; rw [ite_eq_left hh]

theorem abnW_miss (m : Mem) (bo bl : Word) (h : bl ≠ 0)
    (h1 : lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) ≠ rdW (m.arr64 PINS) 12)
    (h2 : lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) ≠ rdW (m.arr64 PINS) 49)
    (h3 : lo32 (rdW (m.arr64 DLP) (rdW (m.arr64 DLP) bo + 1)) ≠ rdW (m.arr64 PINS) 50) :
    abnW m bo bl.toNat = abnW m (bo + 1) (bl - 1).toNat := by
  have hb : bl.toNat = (bl - 1).toNat + 1 := by
    have : bl.toNat ≠ 0 := fun h0 => h (UInt64.toNat_inj.mp (by simpa using h0))
    have := bl.toNat_lt
    rw [UInt64.toNat_sub]; simp; omega
  rw [hb]; simp only [abnW, abnHit]; rw [ite_eq_right (by simp [h1, h2, h3])]

theorem andBlockNamed_specW (p : Prog) (hp : p.lookup "and_block_named" = some andBlockNamed)
    (n : Nat) : ∀ (s₀ : St) (bo bl : Word),
    ⦃fun s => s = s₀⦄ invoke p (exec p n) "and_block_named" [bo, bl]
    ⦃fun r s' => LocEq s' s₀ ∧ s'.mem = s₀.mem ∧ r = [abnW s₀.mem bo bl.toNat]; ⊤⦄ := by
  induction n with
  | zero => intro s₀ bo bl; rw [invoke_eq _ hp]; simp only [callFn, andBlockNamed]; vcgen [exec] <;> grind
  | succ n ih =>
    intro s₀ bo bl
    rw [invoke_eq _ hp]
    simp only [callFn, andBlockNamed]
    sym only [lang_grind, arena_grind] =>
      vcgen [exec, step, evalE, evalC, evalArgs, setLoc, setLocs, ld64, ih] <;>
      finish [lo32, abnW_zero, abnW_hit, abnW_miss]

/-! ## The cut pool -/

theorem trunc_getAP {P : Array Word} {t i : Nat} {v : Word} (h : (trunc P t)[i]? = some v)
    (hi : i ≠ 0) : P[i]? = some v ∧ i ≤ t := by
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.getElem?_extract, Array.size_extract] at h
  rw [ite_eq_right (by omega)] at h
  split at h
  · rename_i hlt
    simp only [Nat.zero_add] at h
    exact ⟨h, by omega⟩
  · cases h

theorem trunc_get_zero {P : Array Word} {t : Nat} {v : Word} (h : (trunc P t)[0]? = some v) :
    v = 0 := by
  simp only [trunc, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds,
    Array.size_extract] at h
  split at h
  · simp at h; exact h.2.symm
  · rename_i hn
    simp only [Array.getElem?_extract] at h
    split at h <;> simp_all

theorem decCIs_succ (a : Array Word) (dn : NIdx → Option ConLeche.Name) (o k : Nat) :
    decCIs a dn o (k + 1) = (do
      let x ← (do let v ← nat? a o; decCI a dn v)
      let xs ← decCIs a dn (o + 1) k
      pure (x :: xs)) := by
  simp only [decCIs, List.range_succ_eq_map, List.mapM_cons, List.mapM_map, Nat.add_zero]
  congr 1; funext x; congr 1
  simp only [Function.comp_def]
  congr 1; funext j; congr 2; omega

theorem decCIs_zero (a : Array Word) (dn : NIdx → Option ConLeche.Name) (o : Nat) :
    decCIs a dn o 0 = some [] := rfl

theorem lo32_of_lt {w : Word} (h : w.toNat < 2 ^ 32) : lo32 w = w := by
  apply UInt64.toNat_inj.mp
  simp only [lo32, UInt64.toNat_and]
  rw [show (UInt64.toNat 4294967295) = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h

/-- The three handles `andPinNameHs` reads, as words of the pin table. -/
def andHs (m : Mem) : List NIdx :=
  [decI (rdW (m.arr64 PINS) 12), decI (rdW (m.arr64 PINS) 49), decI (rdW (m.arr64 PINS) 50)]

/-- **`and_block_named` is `blockAndNamed`** on the block the front's record decodes to (in the
pool cut at `t`), for a slice that does not start at word `0`. -/
theorem abnW_eq {m : Mem} {t : Nat} {dn' : NIdx → Option ConLeche.Name}
    (hP : (m.arr64 DLP).size < 2 ^ 63)
    (h12 : (rdW (m.arr64 PINS) 12).toNat < 2 ^ 32) (h49 : (rdW (m.arr64 PINS) 49).toNat < 2 ^ 32)
    (h50 : (rdW (m.arr64 PINS) 50).toNat < 2 ^ 32) :
    ∀ (k : Nat) (bo : Word) (block : List IConstantInfo),
      decCIs (trunc (m.arr64 DLP) t) dn' bo.toNat k = some block → (1 ≤ bo.toNat ∨ k = 0) →
      abnW m bo k = if blockAndNamed (andHs m) block then 1 else 0 := by
  intro k
  induction k with
  | zero =>
    intro bo block h _
    rw [decCIs_zero] at h; cases h; rfl
  | succ k ih =>
    intro bo block h hbo
    have hbo1 : 1 ≤ bo.toNat := by omega
    rw [decCIs_succ] at h
    simp only [bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c, ⟨v, hv, hc⟩, cs, hcs, rfl⟩ := h
    obtain ⟨w, hw, rfl⟩ : ∃ w, (trunc (m.arr64 DLP) t)[bo.toNat]? = some w ∧ w.toNat = v := by
      simp only [nat?, Option.map_eq_some_iff] at hv; exact hv
    obtain ⟨hwP, -⟩ := trunc_getAP hw (by omega)
    obtain ⟨x, hx, hxl, hname⟩ := decCI_name hc
    obtain ⟨hxP, -⟩ := trunc_getAP hx (by omega)
    have hbolt : bo.toNat < (m.arr64 DLP).size := (Array.getElem?_eq_some_iff.mp hwP).1
    have hwlt : w.toNat + 1 < (m.arr64 DLP).size := (Array.getElem?_eq_some_iff.mp hxP).1
    have e1 : rdW (m.arr64 DLP) bo = w := by simp [rdW, hwP]
    have e2 : rdW (m.arr64 DLP) (w + 1) = x := by
      have : (w + 1).toNat = w.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
      simp [rdW, this, hxP]
    have ebo : (bo + 1).toNat = bo.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
    have ih' := ih (bo + 1) cs (by rw [ebo]; exact hcs) (Or.inl (by omega))
    have hx32 := lo32_of_lt hxl
    have k1 := decI_iff (k := .name) _ _ hxl h12
    have k2 := decI_iff (k := .name) _ _ hxl h49
    have k3 := decI_iff (k := .name) _ _ hxl h50
    have hcon : (andHs m).contains c.name = decide (x = rdW (m.arr64 PINS) 12 ∨
        x = rdW (m.arr64 PINS) 49 ∨ x = rdW (m.arr64 PINS) 50) := by
      simp only [hname, ← k1, ← k2, ← k3]
      simp only [andHs, List.contains_cons, List.contains_nil, Bool.or_false]
      by_cases g1 : (decI x : NIdx) = decI (rdW (m.arr64 PINS) 12) <;>
        by_cases g2 : (decI x : NIdx) = decI (rdW (m.arr64 PINS) 49) <;>
        by_cases g3 : (decI x : NIdx) = decI (rdW (m.arr64 PINS) 50) <;> simp [g1, g2, g3]
    simp only [abnW, abnHit, e1, e2, hx32, blockAndNamed, hcon]
    rw [ih']
    by_cases g : x = rdW (m.arr64 PINS) 12 ∨ x = rdW (m.arr64 PINS) 49 ∨ x = rdW (m.arr64 PINS) 50
    · rw [ite_eq_left g, decide_eq_true g]; rfl
    · rw [ite_eq_right g, decide_eq_false g]; rfl

/-- The twin's `andPinNameHs` at a filled pin table: `andHs`, the state unchanged. -/
theorem andPinNameHs_runW {m : Mem} {a : AState} (hF : PinsFull m a.pins) :
    andPinNameHs.run a = .ok (andHs m, a) := by
  have e1 := pinAt_run hF 11 (by decide)
  have e2 := pinAt_run hF 48 (by decide)
  have e3 := pinAt_run hF 49 (by decide)
  simp only [andPinNameHs, pinAnd, pinAndIntro, pinAndRec, PIN_AND, PIN_AND_INTRO, PIN_AND_REC,
    StateT.run_bind, e1]
  simp only [bind, Except.bind]
  rw [e2]; simp only
  rw [e3]; rfl

end L.Arena
