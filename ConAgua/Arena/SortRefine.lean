import ConAgua.Arena.StoreLib
import ConAgua.Arena.SortStore

/-!
# The `sort` store refines the arena's `sort` tables

The eighth table on the store library, the first expression-store table since `app`: the record
`SortNode { u : LIdx }` (`ConAgua/Arena/SortStore.lean` has the L code). The schema `sortSch`
(`SOREC`, `SOSLOT`, one word per node, counts at `CTL[16 + t]`, tag `2`), the record relation
`SoRecRel` (the word is the level child's handle word), the node hash `sohash`, the lens
`sortLens`; the scratch skip (`skSo`, `soskipW_eq`), the `app` pattern at one field instead of
two. `SortR m a` is the library's `StoreR` for the two `sort` tables.
`internSort_refines`: `intern_sort(u)` refines `internE (.sort (decI u))` under `SortR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order

set_option linter.unusedSimpArgs false

namespace L.Arena

/-- The arena's `sort` cons key. -/
abbrev sortKey (u : LIdx) : SortNode := ⟨u⟩

/-- `a` with the scratch / persistent `sort` table replaced. -/
def withScrSorts (a : AState) (t : Tbl SortNode EIdx UInt64) : AState :=
  { a with store := { a.store with scr := { a.store.scr with sorts := t } } }
def withPersSorts (a : AState) (t : Tbl SortNode EIdx UInt64) : AState :=
  { a with store := { a.store with pers := { a.store.pers with sorts := t } } }

/-- The arena's two `sort` tables. -/
def sortLens : Lens SortNode UInt64 .expr where
  on a := a.store.scratchOn
  getP a := a.store.pers.sorts
  getS a := a.store.scr.sorts
  setP := withPersSorts
  setS := withScrSorts
  on_setP _ _ := rfl
  on_setS _ _ := rfl
  getP_setP _ _ := rfl
  getS_setP _ _ := rfl
  getP_setS _ _ := rfl
  getS_setS _ _ := rfl

/-- The arena's scratch skip at a `sort` view (`EStore.persFindMaybe`). -/
def skSo (a : AState) (u : LIdx) : Bool :=
  if a.store.scratchOn then !u.isPersistent else false

/-- The arena's persistent probe at a `sort` view, after the skip. -/
def pfSo (a : AState) (u : LIdx) : Option EIdx :=
  if skSo a u then none else a.store.pers.sorts.cons[sortKey u]?

theorem persFindMaybe_sort (a : AState) (u : LIdx) :
    a.store.persFindMaybe (.sort u) = pfSo a u := by
  simp [EStore.persFindMaybe, pfSo, skSo, EStore.eViewHasScratchChild, ETables.find?, Tbl.find?]

/-- `internE` at a `sort` node is the library's protocol, the persistent probe after the skip. -/
theorem internE_sort_run (u : LIdx) (a : AState) :
    (internE (.sort u)).run a =
      protoRun sortLens (sortKey u) ETag.sort (pfSo a u) (a.store.derOfView (.sort u))
        (.native "arena: expression constructor array full") a := by
  simp only [internE, internNodeE, EStore.find?, EStore.intern, ETables.find?, Tbl.find?,
    ETables.sizeOf, ETables.push, StateT.run_bind, StateT.run_get, pure_bind, persFindMaybe_sort]
  cases hp : pfSo a u <;> cases hs : a.store.scratchOn <;>
    cases hc : a.store.scr.sorts.cons[sortKey u]? <;>
    simp only [hp, hs, hc, Bool.false_eq_true, ↓reduceIte, sortKey, ite_self, protoRun, sortLens] <;>
    (try split) <;> simp_all [StateT.run_set, StateT.run_pure, withScrSorts, withPersSorts, fail,
      throwThe, MonadExceptOf.throw, StateT.run, Functor.map, StateT.map, set, StateT.set,
      StateT.lift, bind, Except.bind, Except.map, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `sort` tables -/

/-- The `sort` schema: `SOREC`, `SOSLOT`, one word per node, the counts at `CTL[16 + t]`. -/
def sortSch : Schema := ⟨SOREC, SOSLOT, 1, 2, 16, ETag.sort⟩

theorem sortSch_wf : sortSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem fld_sort0 (m : Mem) (t i : Word) :
    fld sortSch m t i 0 = rdW (m.arr64 SOREC) (i * 2 + t) := by
  simp [fld, Schema.ad, sortSch]

/-- Node `i` of tier `t` holds `sort k.u`: its word is the child's handle word. -/
def SoRecRel (m : Mem) (t i : Word) (k : SortNode) : Prop :=
  rdW (m.arr64 SOREC) (i * 2 + t) = k.u.word.toUInt64

/-- The hash of node `i` of tier `t`. -/
def sohash (m : Mem) (t i : Word) : Word := sortHashW (rdW (m.arr64 SOREC) (i * 2 + t))

/-- **The state relation** of the `sort` store: the library's relation for the two `sort`
tables. -/
def SortR (m : Mem) (a : AState) : Prop :=
  StoreR sortSch SoRecRel sohash m a.store.scratchOn a.store.pers.sorts a.store.scr.sorts

/-- A node's relation and hash depend only on its word. -/
theorem sortFrame : RFrame sortSch SoRecRel sohash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_sort0, fld_sort0] at h0
  exact ⟨fun a h => by simpa only [SoRecRel, h0] using h, by simp only [sohash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `sort_find` on node `i` of tier `t`. -/
def soMt (m : Mem) (u t i : Word) : Bool := somatchW (m.arr64 SOREC) t i u

section query
variable (m : Mem) (u : Word) (hu : u.toNat < 2 ^ 32)

include hu in
/-- **Matching is equality of `sort` nodes.** -/
theorem sortMatchOK : MatchOK SoRecRel (soMt m u) m (sortKey (decI u)) := by
  intro t i k hr
  have := word_decI k.u u hu
  obtain ⟨ku⟩ := k
  grind [soMt, somatchW, SoRecRel]

theorem sortHomeOK : HomeOK sohash (soMt m u) m (sortHashW u) := by
  intro t i hm
  simp only [soMt, somatchW, beq_iff_eq] at hm
  simp only [sohash, hm]

include hu in
/-- The record `sort_push` writes holds the node. -/
theorem sortNewOK : NewOK sortSch SoRecRel sohash m [u] (sortKey (decI u)) (sortHashW u) := by
  intro t j ht hroom
  have e : fld sortSch (pushG sortSch m t [u] j (cntW sortSch m t)) t
      (cntW sortSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_pushG sortSch sortSch_wf] <;> simp only [sortSch, Schema.ad] at * <;> grind
  rw [fld_sort0] at e
  have := word_decI (decI u : LIdx) u hu
  simp only [SoRecRel, sohash, sortKey, e]
  grind

end query

/-! ## The bridges from the L models -/

theorem soprobeW_arm (m : Mem) (u t : Word) :
    ∀ j d, soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) t u (baseW m t) (nSlotsSo m) j d =
      probeArm sortSch m t (soMt m u t) (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) t u (baseW m t) (nSlotsSo m)) j d := by
  intro j d; rw [soprobeW]; rfl

theorem sopushOK_room (m : Mem) (t : Word) (h : sopushOK m t = true) : PushRoom sortSch m t := by
  simp only [sopushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 SOREC) 1
  simp only [PushRoom, cntW, socnt, sortSch, len64_eq] at *
  grind

theorem sopushMem_eq (m : Mem) (t u j c : Word) :
    sopushMem m t u j c = pushG sortSch m t [u] j c := by
  simp [sopushMem, pushG, wrRec, Schema.ad, sortSch]

theorem sointernW_eq (m : Mem) (u : Word) :
    sointernW m u = internM sortSch m (soskipW m u) (sopushOK m) [u]
      (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 0 u (baseW m 0) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0)
      (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 1 u (baseW m 1) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0) := by
  have e0 : ∀ x, hdW sortSch.tag.toUInt64 0 x = sortP + x := fun x => by
    simp [hdW, sortSch, sortP, ETag.sort]
  have e1 : ∀ x, hdW sortSch.tag.toUInt64 1 x = sortS + x := fun x => by
    simp [hdW, sortSch, sortS, ETag.sort]
  simp only [sointernW, internM, sopushMem_eq, e0, e1]
  rfl

/-- The L skip test is the arena's. -/
theorem soskipW_eq (m : Mem) (a : AState) (u : Word) (hu : u.toNat < 2 ^ 32)
    (hfl : (rdW (m.arr64 CTL) 1 != 0) = a.store.scratchOn) :
    (soskipW m u = 0) = (skSo a (decI u) = false) := by
  simp only [soskipW, skSo, isPersistent_decI (k := .level) u hu, ← hfl]
  grind

/-! ## `intern_sort` refines `internE (.sort _)` -/

section intern
variable (m : Mem) (a : AState) (hR : SortR m a) (u : Word) (hu : u.toNat < 2 ^ 32)

include hR hu in
/-- **`intern_sort`'s model refines the arena's `internE` at a `sort` node.** -/
theorem sointern_correct (w : Word) (m' : Mem) (hI : sointernW m u = some (w, m')) :
    AM.ok (internE (.sort (decI u))) a ∧
    SortR m' (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI w := by
  rw [sointernW_eq] at hI
  exact intern_correctG sortSch SoRecRel sohash sortSch_wf sortFrame sortLens a m hR _ _ _ _ _
    (internE_sort_run _ a) (skSo a (decI u)) rfl _ (soskipW_eq m a u hu hR.2.1)
    (fun h => by simp only [skSo] at h; split at h <;> simp_all [sortLens]) _ _
    (sortMatchOK m u hu) (sortHomeOK m u) _ _
    (probe_homeG sortSch m 0 _ _ (soprobeW_arm m u 0) _)
    (probe_homeG sortSch m 1 _ _ (soprobeW_arm m u 1) _) _ (sopushOK_room m) _ rfl
    (sortNewOK m u hu) w m' hI

end intern

/-- `intern_sort` refines `internE (.sort _)` under `SortR`. -/
theorem internSort_refines (p : Prog) (hpf : p.lookup "sort_find" = some sortFind)
    (hpp : p.lookup "sort_push" = some sortPush) (hp : p.lookup "intern_sort" = some internSort)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : SortR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_sort" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.sort (decI u))) a₀ ∧
      SortR s'.mem (AM.st (internE (.sort (decI u))) a₀) ∧
      AM.res (internE (.sort (decI u))) a₀ = decI (r.headD 0); ⊤⦄ := by
  apply M.triple_of_run
  intro s r s' hs hrun
  obtain ⟨hloc, hI⟩ := M.of_run (P := fun s => s = s₀) hs hrun (internSort_spec p hpf hpp hp n s₀ u)
  subst hs
  exact ⟨hloc, sointern_correct s.mem a₀ hR u hu _ _ hI⟩

end L.Arena
