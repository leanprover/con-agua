module

public import ConAgua.Front.IndInstallRefine
public import Std.Tactic.BVDecide.Normalize.Prop
import ConAgua.Front.IndApplyRefine
import ConAgua.Front.IndApplyRefine2

@[expose] public section

/-!
# `install_ind_d` refines `installIndD`, II: the type and constructor records

`typeW_twin`, `ctorRW_twin`: `ind_type`/`ind_ctor` allocate a record above `DLP`'s top and write
it; it decodes (`decCI`) as the twin's `indInfo`/`ctorInfo` constant in any pool that agrees with
the memory from the record on (`RecAt`).
-/

open L.Arena
open ConRon.Arena
open ConRon.Arena.Frontend
open ConLeche.Frontend (IndCtorRec IndTypeRec IndRecRec CVRec RuleRec)
open ConAgua.Front.FieldsLink
open L.Front.Fields (listN itemsN)


namespace L.Front.Ind

/-- The value of a twin computation that runs `.ok` (else `default`). -/
def resOf {α : Type} [Inhabited α] (x : AM α) (a : AState) : α :=
  match x.run a with
  | .ok (c, _) => c
  | .error _ => default

theorem resOf_eq {α : Type} [Inhabited α] {x : AM α} {a a' : AState} {c : α}
    (h : x.run a = .ok (c, a')) : resOf x a = c := by
  simp [resOf, h]

/-- **The constant record at `q`** decodes as `ci` in every pool that holds `m`'s words from `q`
to the top. -/
def RecAt (m : Mem) (q : Nat) (ci : IConstantInfo) : Prop :=
  ∀ P, AgreesFrom P m q → decCI (aread P) (fun _ => none) q = some ci

theorem RecAt.keep {m m' : Mem} {q : Nat} {ci : IConstantInfo} (h : RecAt m q ci)
    (ht : topN m DLP ≤ topN m' DLP) (hk : ∀ i, q ≤ i → i ≤ topN m DLP → wd m' DLP i = wd m DLP i) :
    RecAt m' q ci :=
  fun P hP => h P (fun i h1 h2 => by rw [hP i h1 (Nat.le_trans h2 ht), hk i h1 h2])

theorem wd_set_ne (m : Mem) (A : ArrId) (i v : Word) (j : Nat) (h : i.toNat ≠ j) :
    wd (m.set64 A i v) A j = wd m A j := by
  rw [wd_setA]; simp [h]

theorem wd_set_eq (m : Mem) (A : ArrId) (i v : Word) (j : Nat) (h : i.toNat = j)
    (hs : j < (m.arr64 A).size) : wd (m.set64 A i v) A j = v := by
  rw [wd_setA]; simp [h, hs]

theorem range_map_eq {α β : Type} (l : List α) (f : Nat → β) (g : α → β)
    (h : ∀ j (hj : j < l.length), f j = g l[j]) : (List.range l.length).map f = l.map g := by
  apply List.ext_getElem (by simp)
  intro j h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range]; exact h j h1

/-- A pool agreeing with `m` from `q` holds word `i` (in range). -/
theorem AgreesFrom.get {P : Array Word} {m : Mem} {q : Nat} (h : AgreesFrom P m q) {i : Nat}
    (h1 : q ≤ i) (h2 : i ≤ topN m DLP) : P[i]? = some (wd m DLP i) := h i h1 h2

/-! ## The capabilities -/

/-- `ind_caps`' fifteen words decode as the default capabilities. -/
theorem capsM_dec (m : Mem) (q : Word) (hs : q.toNat + 15 ≤ (m.arr64 DLP).size) (hq : q.toNat + 15 < 2 ^ 64)
    (P : Array Word) (dn : NIdx → Option ConLeche.Name)
    (h : ∀ k, k < 15 → P[q.toNat + k]? = some (wd (capsM m q) DLP (q.toNat + k))) :
    decCaps (aread P) dn q.toNat = some {} := by
  sorry

/-- `ind_caps` writes only its fifteen words. -/
theorem capsM_out (m : Mem) (q : Word) (hq : q.toNat + 15 < 2 ^ 64) (j : Nat)
    (hj : j < q.toNat ∨ q.toNat + 15 ≤ j) : wd (capsM m q) DLP j = wd m DLP j := by
  unfold capsM; rw [wd_set_ne _ DLP (q + 14) _ j (by rw [widx2 q 14 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 13) _ j (by rw [widx2 q 13 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 12) _ j (by rw [widx2 q 12 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 11) _ j (by rw [widx2 q 11 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 10) _ j (by rw [widx2 q 10 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 9) _ j (by rw [widx2 q 9 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 8) _ j (by rw [widx2 q 8 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 7) _ j (by rw [widx2 q 7 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 6) _ j (by rw [widx2 q 6 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 5) _ j (by rw [widx2 q 5 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 4) _ j (by rw [widx2 q 4 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 3) _ j (by rw [widx2 q 3 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 2) _ j (by rw [widx2 q 2 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP (q + 1) _ j (by rw [widx2 q 1 (by simp; omega)]; simp only [UInt64.reduceToNat]; omega), wd_set_ne _ DLP q _ j (by omega)]

theorem capsM_frame (m : Mem) (q : Word) : MemFrame [DLP] [] m (capsM m q) := by
  unfold capsM
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  refine MemFrame.trans ?_ (MemFrame.set64 _ DLP (by decide) _ _)
  exact MemFrame.set64 _ DLP (by decide) _ _

theorem capsM_size (m : Mem) (q : Word) : ((capsM m q).arr64 DLP).size = (m.arr64 DLP).size :=
  (capsM_frame m q).size DLP

/-! ## The type and constructor records -/

/-- The twin's constant of a type record (`installIndD`'s `types`). -/
def tyT (st : StateD) (t : IndTypeRec) : AM IConstantInfo := do
  pure (IConstantInfo.indInfo (← parseCVD st t.cv) {})

/-- The twin's constant of a constructor record (`installIndD`'s `ctors`). -/
def ctT (st : StateD) (c : IndCtorRec) : AM IConstantInfo := do
  pure (IConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)

theorem rdW_wdI (m : Mem) (A : ArrId) (t w : Word) (h : t.toNat + w.toNat < 2 ^ 64) :
    rdW (m.arr64 A) (t + w) = wd m A (t.toNat + w.toNat) := by
  simp only [rdW, wd, widx2 t w h]

/-- **`ind_type` against the twin's type constant.** -/
theorem typeW_twin {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {t q : Word} {ty : IndTypeRec} (hF : CVF b m t.toNat ty.cv) (ht : t.toNat + 3 < 2 ^ 63)
    (h : typeW b.data m t = some (q, m')) :
    (tyT st ty).run a = .ok (resOf (tyT st ty) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
      LkR m' st ∧ RecAt m' q.toNat (resOf (tyT st ty) a) := by
  sorry

/-- **`ind_ctor` against the twin's constructor constant.** -/
theorem ctorRW_twin {b : ByteArray} {m m' : Mem} {st : StateD} (a : AState) (hD : LkR m st)
    {c q : Word} {ct : IndCtorRec} (hF : CtF b m c.toNat ct) (hc : c.toNat + 6 < 2 ^ 63)
    (h : ctorRW b.data m c = some (q, m')) :
    (ctT st ct).run a = .ok (resOf (ctT st ct) a, a) ∧ PExt m m' ∧ q.toNat = topN m DLP + 1 ∧
      LkR m' st ∧ RecAt m' q.toNat (resOf (ctT st ct) a) := by
  sorry

end L.Front.Ind
