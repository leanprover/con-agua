import ConAgua.Arena.StoreLib
import ConAgua.Arena.SimLib
import ConAgua.Arena.SortStore
import ConAgua.Arena.LpColRel

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
    sopushMem m t u j c = (pushG sortSch m t [u] j c).set64 SOLP (c * 2 + t) (lvlHPW m u) := by
  simp [sopushMem, pushG, wrRec, Schema.ad, sortSch]

theorem sointernW_eq (m : Mem) (u : Word) :
    sointernW m u = internMD sortSch SOLP (lvlHPW m u) m (soskipW m u) (sopushOK m) [u]
      (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 0 u (baseW m 0) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0)
      (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 1 u (baseW m 1) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0) := by
  have e0 : ∀ x, hdW sortSch.tag.toUInt64 0 x = sortP + x := fun x => by
    simp [hdW, sortSch, sortP, ETag.sort]
  have e1 : ∀ x, hdW sortSch.tag.toUInt64 1 x = sortS + x := fun x => by
    simp [hdW, sortSch, sortS, ETag.sort]
  simp only [sointernW, internMD, sopushMem_eq, e0, e1]
  rfl

/-- **What `intern_sort` changes**: the table's arrays, the `lp` column, the counts. -/
theorem sointernW_frame (m : Mem) (u w : Word) (m' : Mem) (hI : sointernW m u = some (w, m')) :
    MemFrame [SOREC, SOSLOT, SOLP] [16, 17] m m' := by
  rw [sointernW_eq] at hI
  exact internMD_frame sortSch sortSch_wf SOLP (by decide) _ _ _ _ _ _ _ _ _ hI

/-- `intern_sort`'s model as the library's interning and the `mk_*` tail (`mkK`), given the
count words. -/
theorem sointernW_eqK (m : Mem) (u : Word) (hctl : sortSch.ca.toNat + 2 ≤ (m.arr64 CTL).size) :
    sointernW m u = mkK SOLP sortSch.ca (cnt2 m sortSch.ca) (lvlHPW m u)
      (internM sortSch m (soskipW m u) (sopushOK m) [u]
        (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 0 u (baseW m 0) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0)
        (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 1 u (baseW m 1) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0)) := by
  rw [sointernW_eq]
  refine internMD_mkK sortSch sortSch_wf _ _ _ _ _ _ _ _ hctl (fun t ht hp => ?_)
  simp only [sopushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
  obtain ⟨⟨⟨h1, -⟩, h2⟩, -⟩ := hp
  exact ⟨h1, col_room _ _ _ ht h1 h2⟩

theorem sortLocal : RLocal sortSch SoRecRel sohash [] [] := by
  intro m m' hra _ _; simp only [sortSch] at hra
  exact ⟨fun t i k h => by simpa only [SoRecRel, hra] using h, fun t i => by simp only [sohash, hra]⟩

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
/-- The library's half of `intern_sort` (before the `lp` column). -/
theorem sointern_core (w : Word) (m₁ : Mem)
    (hI : internM sortSch m (soskipW m u) (sopushOK m) [u]
        (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 0 u (baseW m 0) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0)
        (soprobeW (m.arr64 SOSLOT) (m.arr64 SOREC) 1 u (baseW m 1) (nSlotsSo m) (homeW (sortHashW u) (nSlotsSo m)) 0) =
      some (w, m₁)) :
    AM.ok (internE (.sort (decI u))) a ∧
    SortR m₁ (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI w :=
  intern_correctG sortSch SoRecRel sohash sortSch_wf sortFrame sortLens a m hR _ _ _ _ _
    (internE_sort_run _ a) (skSo a (decI u)) rfl _ (soskipW_eq m a u hu hR.2.1)
    (fun h => by simp only [skSo] at h; split at h <;> simp_all [sortLens]) _ _
    (sortMatchOK m u hu) (sortHomeOK m u) _ _
    (probe_homeG sortSch m 0 _ _ (soprobeW_arm m u 0) _)
    (probe_homeG sortSch m 1 _ _ (soprobeW_arm m u 1) _) _ (sopushOK_room m) _ rfl
    (sortNewOK m u hu) w m₁ hI

include hR hu in
/-- **`intern_sort`'s model refines the arena's `internE` at a `sort` node.** -/
theorem sointern_correct (w : Word) (m' : Mem) (hI : sointernW m u = some (w, m')) :
    AM.ok (internE (.sort (decI u))) a ∧
    SortR m' (AM.st (internE (.sort (decI u))) a) ∧
    AM.res (internE (.sort (decI u))) a = decI w := by
  rw [sointernW_eqK m u hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := sointern_core m a hR u hu w m₁ h₁
  exact ⟨hok, storeR_frame sortSch SoRecRel sohash sortSch_wf [] [] sortLocal [SOLP] []
    (by simp [Apart, sortSch, SOREC, SOSLOT, SOLP, SCB]) m₁ m'
    (derPutW_frame SOLP (by decide) _ m₁ m' _ _ _ hput) _ _ _ hX, hres⟩

include hR hu in
/-- **The `lp` column across `intern_sort`**: the new node's word is the level's `hasParam` bit
(`hb`, `lvlHPW_ok` under `ArenaR`). -/
theorem sointern_lp (hC : ColT2 sortLens SOLP lpW m a)
    (hb : lvlHPW m u = b2w (a.store.lder (decI u)).hasParam) (w : Word) (m' : Mem)
    (hI : sointernW m u = some (w, m')) :
    ColT2 sortLens SOLP lpW m' (AM.st (internE (.sort (decI u))) a) := by
  rw [sointernW_eqK m u hR.1.1] at hI
  obtain ⟨m₁, h₁, hput⟩ := mkK_split _ _ _ _ _ _ _ hI
  obtain ⟨hok, hX, hres⟩ := sointern_core m a hR u hu w m₁ h₁
  have hcs := AM.proto_casesG sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok
  have hfr : m₁.arr64 SOLP = m.arr64 SOLP :=
    (internM_frame _ sortSch_wf _ _ _ _ _ _ _ _ h₁).1 SOLP (by simp [sortSch, SOREC, SOSLOT, SOLP])
      (by decide)
  exact colMk sortSch sortSch_wf SoRecRel sohash sortLens SOLP lpW m m₁ m' a _ _ _ _ _ _ hR hX hC hfr
    hcs hres.symm (by rw [hb, lpW, lp_derSort]) hput

end intern

/-- `intern_sort` refines `internE (.sort _)` under `SortR`. -/
theorem internSort_refines (p : Prog) (hpf : p.lookup "sort_find" = some sortFind)
    (hpp : p.lookup "sort_push" = some sortPush) (hp : p.lookup "intern_sort" = some internSort)
    (a₀ : AState) (n : Nat) (s₀ : St) (u : Word) (hR : SortR s₀.mem a₀) (hu : u.toNat < 2 ^ 32) :
    ⦃fun s => s = s₀⦄
    invoke p (exec p n) "intern_sort" [u]
    ⦃fun r s' => LocEq s' s₀ ∧ AM.ok (internE (.sort (decI u))) a₀ ∧
      SortR s'.mem (AM.st (internE (.sort (decI u))) a₀) ∧
      AM.res (internE (.sort (decI u))) a₀ = decI (r.headD 0); ⊤⦄ :=
  Sim.tripleD (internSort_spec p hpf hpp hp n s₀ u)
    (Sim.ofOkD (sointern_correct s₀.mem a₀ hR u hu))

end L.Arena
