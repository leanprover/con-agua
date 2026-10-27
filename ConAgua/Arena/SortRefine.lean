import ConAgua.Arena.SortStore
import ConAgua.Arena.LpColRel
import Std.Tactic.BVDecide.Normalize.BitVec
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The `sort` store refines the arena's `sort` tables

The eighth table on the store library, the first expression-store table since `app`: the record
`SortNode { u : LIdx }` (`ConAgua/Arena/SortStore.lean` has the L code). The schema `sortSch`
(`SOREC`, `SOSLOT`, one word per node, counts at `CTL[16 + t]`, tag `2`), the record relation
`SoRecRel` (the word is the level child's handle word), the node hash `sohash`, the lens
`sortLens`; the scratch skip (`skSo`, `soskipW_eq`), the `app` pattern at one field instead of
two. `SortR m a` is the library's `ConsR` for the two `sort` tables.
`internSort_refines`: `intern_sort(u)` refines `internE (.sort (decI u))` under `SortR`.

Not represented: the derived column and every other table.
-/

open ConRon.Arena
open Std.WP
open scoped Lean.Order


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
    simp only [hs, hc, Bool.false_eq_true, ↓reduceIte, sortKey, protoRun, sortLens] <;>
    (try split) <;> simp_all [withScrSorts, withPersSorts, fail,
      throwThe, MonadExceptOf.throw, StateT.run, set, StateT.set,
      StateT.lift, bind, Except.bind, pure, Except.pure, StateT.bind, StateT.pure]

/-! ## The relation between L memory and the arena's `sort` tables -/

/-- The `sort` schema: `SOREC`, `SOSLOT`, one word per node, the counts at `CTL[16 + t]`. -/
def sortSch : Schema := ⟨SOREC, SOSLOT, 1, 16, ETag.sort⟩

theorem sortSch_wf : sortSch.WF :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem fld_sort0 (m : Mem) (t i : Word) :
    fld sortSch m t i 0 = rdW (m.arr64 (tierA SOREC t)) i := by
  simp [fld, Schema.ad, sortSch]

/-- Node `i` of tier `t` holds `sort k.u`: its word is the child's handle word. -/
def SoRecRel (m : Mem) (t i : Word) (k : SortNode) : Prop :=
  tfld m SORT t i 0 = k.u.word.toUInt64

/-- `SoRecRel` in the raw words (inside the store library). -/
theorem SoRecRel_raw (m : Mem) (t i : Word) (k : SortNode) :
    SoRecRel m t i k ↔
    rdW (m.arr64 (tierA SOREC t)) i = k.u.word.toUInt64
  := Iff.rfl

/-- **The state relation** of the `sort` store: the library's relation for the two `sort`
tables. -/
def SortR (m : Mem) (a : AState) : Prop :=
  ConsR sortCS SoRecRel m a.store.scratchOn a.store.pers.sorts a.store.scr.sorts

/-- A node's relation and hash depend only on its word. -/
theorem sortFrame : RFrame sortSch SoRecRel sohash := by
  intro m m' t i _ hf
  have h0 := hf 0 (by decide)
  rw [fld_sort0, fld_sort0] at h0
  exact ⟨fun a h => by simpa only [SoRecRel_raw, h0] using h, by simp only [sohash, h0]⟩

/-! ## The query's obligations -/

/-- The match of `sort_find` on node `i` of tier `t`. -/
def soMt (m : Mem) (u t i : Word) : Bool := somatchW (m.arr64 (tierA SOREC t)) t i u

section query
variable (m : Mem) (u : Word) (hu : u.toNat < 2 ^ 32)

include hu in
/-- **Matching is equality of `sort` nodes.** -/
theorem sortMatchOK : MatchOK SoRecRel (soMt m u) m (sortKey (decI u)) := by
  intro t i k hr
  have := word_decI k.u u hu
  obtain ⟨ku⟩ := k
  grind [soMt, somatchW, SoRecRel_raw]

theorem sortHomeOK : HomeOK sohash (soMt m u) m (sortHashW u) := by
  intro t i hm
  simp only [soMt, somatchW, beq_iff_eq] at hm
  simp only [sohash, hm]

include hu in
/-- The record `sort_push` writes holds the node. -/
theorem sortNewOK : NewOKR sortSch SoRecRel sohash m [u] (sortKey (decI u)) (sortHashW u) := by
  intro t ht hroom _
  have e : fld sortSch (newRecM sortSch m t [u]) t
      (cntW sortSch m t) 0 = u := by
    have := hroom.1
    have := hroom.2
    rw [fld_newRecM sortSch sortSch_wf] <;> simp only [sortSch, Schema.ad] at * <;> grind
  rw [fld_sort0] at e
  have := word_decI (decI u : LIdx) u hu
  simp only [SoRecRel_raw, sohash, sortKey, e]
  grind

end query

/-! ## The bridges from the L models -/

theorem sopushOK_room (m : Mem) (t : Word) (h : sopushOK m t = true) : PushRoom sortSch m t := by
  simp only [sopushOK, Bool.and_eq_true, decide_eq_true_eq] at h
  have := UInt64.toNat_shiftRight (m.len64 (tierA SOREC t)) 0
  simp only [PushRoom, cntW, socnt, sortSch, len64_eq] at *
  grind

/-- **The `sort` table's shape.** -/
theorem sortCS_wf : sortCS.WF where
  sch := sortSch_wf
  P := by decide
  S := by decide
  col A h := by
    simp only [sortCS, Option.some.injEq] at h; subst h
    exact ⟨by decide, by decide, by decide, fun m u k x t i => by
      simp only [sortCS, sohash, Mem.arr64_set64_ne _ _ _ _ _
        (tierA_ne (by decide) (by decide) (show SOREC ≠ SOLP by decide) t u)]⟩
  room m t h := (sopushOK_room m t ((sopushOK_eqC m t).trans h)).2
  colRoom A h m t ht hp := by
    simp only [sortCS, Option.some.injEq] at h; subst h
    rw [← sopushOK_eqC] at hp
    simp only [sopushOK, Bool.and_eq_true, decide_eq_true_eq] at hp
    exact colRoom_of m SOLP _ t hp.2
  colLt A h := by
    simp only [sortCS, Option.some.injEq] at h; subst h; decide
  vs ks h hk := by simp [pushArgs, sortCS, hk]
  ex _ := {
    nk := by decide
    nkw := by decide
    kpk := fun h => absurd h (by decide)
    mt := by
      intro m ks h t i hl
      obtain ⟨a, rfl⟩ := list_one ks (by simpa [sortCS] using hl)
      simp [sortCS, somatchW, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl]
    hs := by intro m t i; simp [sortCS, somatchW, sohash, fieldsL, kfld, fld, Schema.ad, ConsSch.sch, List.range_succ, show UInt64.ofNat 0 = 0 from rfl]
    qh := fun _ _ _ => rfl
    vs := by intro ks h hl f hf; simp [pushArgs, sortCS, nkW, recK] at hf ⊢ <;> omega }

/-- `SoRecRel` does not read the column. -/
theorem sortColFree : ColFree sortCS SoRecRel := by
  intro A h m u k x t i a hr
  simp only [sortCS, Option.some.injEq] at h; subst h
  simpa only [SoRecRel_raw, Mem.arr64_set64_ne _ _ _ _ _ (tierA_ne (by decide) (by decide) (show SOREC ≠ SOLP by decide) t u)] using hr

/-- **What `intern_sort` changes**: the table's arrays, the `lp` column, the counts. -/
theorem sointernW_frame (m : Mem) (u w : Word) (m' : Mem) (hI : sointernW m u = some (w, m')) :
    MemFrame [SOREC, tier1 SOREC, SOSLOT, tier1 SOSLOT, SOLP, tier1 SOLP] [16, 17] m m' :=
  consInternM_frame sortCS_wf hI

theorem sortLocal : RLocal sortSch SoRecRel sohash [] [] := by
  intro m m' hra _ _; simp only [sortSch] at hra
  exact ⟨fun t i k h => by simpa only [SoRecRel_raw, hra] using h, fun t i => by simp only [sohash, hra]⟩

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
    AM.res (internE (.sort (decI u))) a = decI w :=
  consIntern_correct sortCS_wf sortFrame sortColFree sortLens a hR _ _ _ _ _
    (internE_sort_run _ a) (skSo a (decI u)) rfl [u]
    (soskipW_eq m a u hu (ConsR.flag hR))
    (fun h => by simp only [skSo] at h; split at h <;> simp_all [sortLens])
    ⟨rfl, sortMatchOK m u hu, sortHomeOK m u, sortNewOK m u hu⟩ w m' hI

include hR hu in
/-- **The `lp` column across `intern_sort`**: the new node's word is the level's `hasParam` bit
(`hb`, `lvlHPW_ok` under `ArenaR`). -/
theorem sointern_lp (hC : ColT2 sortLens SOLP lpW m a)
    (hb : lvlHPW m u = b2w (a.store.lder (decI u)).hasParam) (w : Word) (m' : Mem)
    (hI : sointernW m u = some (w, m')) :
    ColT2 sortLens SOLP lpW m' (AM.st (internE (.sort (decI u))) a) := by
  obtain ⟨hok, hX, hres⟩ := sointern_correct m a hR u hu w m' hI
  have hcs := AM.proto_casesG sortLens _ _ _ _ _ _ a (internE_sort_run _ a) hok
  exact colMkC sortCS_wf rfl sortLens lpW hR hX hC hI hcs
    (by show lvlHPW m u = _; rw [hb, lpW, lp_derSort])

end intern

end L.Arena
